import Mathlib
import Architect

set_option linter.all false
set_option maxHeartbeats 500000

open Classical

@[blueprint "def:erasureFrac"
  (statement := /-- Let $\Sigma$ be a finite alphabet and $n \in \mathbb{N}$. A partially erased word is a map $\widetilde{g} : \{0,\dots,n-1\} \to \Sigma \cup \{\bot\}$, where $\bot$ denotes an erasure. Its erasure fraction is $s(\widetilde{g}) = \frac{1}{n}\,\bigl\lvert\{\, i : \widetilde{g}_i = \bot \,\}\bigr\rvert$, the fraction of coordinates carrying $\bot$. -/)
  (title := /-- Erasure fraction of a partially erased word -/)
  (latexEnv := "definition")]
noncomputable def erasureFrac {n : ℕ} {α : Type*} [DecidableEq α]
    (g : Fin n → Option α) : ℝ :=
  ((Finset.univ.filter (fun i => g i = none)).card : ℝ) / (n : ℝ)

@[blueprint "def:erasureDist"
  (statement := /-- Let $\widetilde{g} : \{0,\dots,n-1\} \to \Sigma \cup \{\bot\}$ be a partially erased word and $h \in \Sigma^n$ a word. The erasure distance from $\widetilde{g}$ to $h$ is $\Delta(\widetilde{g}, h) = \frac{1}{n}\,\bigl\lvert\{\, i : \widetilde{g}_i \neq \bot \text{ and } \widetilde{g}_i \neq h_i \,\}\bigr\rvert$, the fraction of all $n$ coordinates that are not erased and on which $\widetilde{g}$ and $h$ disagree. -/)
  (title := /-- Erasure distance to a partially erased word -/)
  (latexEnv := "definition")]
noncomputable def erasureDist {n : ℕ} {α : Type*} [DecidableEq α]
    (g : Fin n → Option α) (h : Fin n → α) : ℝ :=
  ((Finset.univ.filter (fun i => g i ≠ none ∧ g i ≠ some (h i))).card : ℝ) / (n : ℝ)

@[blueprint "def:AvgRadiusLDCErasures"
  (statement := /-- Let $\delta, \varepsilon \in \mathbb{R}$ and $k \in \mathbb{N}$. A code $\mathcal{C} \subseteq \Sigma^n$ is $(\delta, k, \varepsilon)$ average-radius list decodable with erasures if for every partially erased word $\widetilde{g}$, with erasure fraction $s = s(\widetilde{g})$ as in \cref{def:erasureFrac}, and every nonempty finite list $\mathcal{H} \subseteq \mathcal{C}$ with $1 \le \lvert \mathcal{H}\rvert \le k$, one has $\sum_{h \in \mathcal{H}} \Delta(\widetilde{g}, h) \ge (\lvert \mathcal{H}\rvert - 1)\,(\delta - s - \varepsilon)$, where $\Delta$ is the erasure distance of \cref{def:erasureDist}. The list is required to be nonempty: for $\mathcal{H} = \varnothing$ the asserted inequality reduces to $\delta - s - \varepsilon \le 0$, which is not part of the intended notion, so the empty list is excluded. -/)
  (title := /-- Average-radius list decodable with erasures -/)
  (latexEnv := "definition")]
def AvgRadiusLDCErasures {n : ℕ} {α : Type*} [DecidableEq α]
    (C : Set (Fin n → α)) (δ : ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ (g : Fin n → Option α) (H : Finset (Fin n → α)),
    (↑H : Set (Fin n → α)) ⊆ C → 1 ≤ H.card → H.card ≤ k →
    ((H.card : ℝ) - 1) * (δ - erasureFrac g - ε) ≤ ∑ h ∈ H, erasureDist g h

@[blueprint "def:ExpanderGraph"
  (statement := /-- An $(n, d, \lambda)$-expander is a balanced $d$-regular bipartite graph with left and right vertex sets $L = R = \{0,\dots,n-1\}$, specified by neighbourhoods $N(\ell) \subseteq R$ satisfying $\lvert N(\ell)\rvert = d$ for every $\ell \in L$ and $\lvert\{\, \ell \in L : r \in N(\ell) \,\}\rvert = d$ for every $r \in R$, and obeying the expander mixing inequality: writing $E(S, T) = \sum_{\ell \in S} \lvert N(\ell) \cap T\rvert$ for the number of edges between $S \subseteq L$ and $T \subseteq R$, one has $\bigl\lvert E(S, T) - \tfrac{d}{n}\,\lvert S\rvert\,\lvert T\rvert \bigr\rvert \le \lambda\, d\, n$ for all $S \subseteq L$ and $T \subseteq R$. -/)
  (title := /-- $(n,d,\lambda)$-expander graph -/)
  (latexEnv := "definition")]
structure ExpanderGraph (n d : ℕ) (lam : ℝ) where
  nbrs : Fin n → Finset (Fin n)
  leftReg : ∀ ℓ : Fin n, (nbrs ℓ).card = d
  rightReg : ∀ r : Fin n, (Finset.univ.filter (fun ℓ : Fin n => r ∈ nbrs ℓ)).card = d
  mixing : ∀ S T : Finset (Fin n),
      |(∑ ℓ ∈ S, ((nbrs ℓ ∩ T).card : ℝ))
          - (d : ℝ) / (n : ℝ) * (S.card : ℝ) * (T.card : ℝ)|
        ≤ lam * (d : ℝ) * (n : ℝ)

@[blueprint "def:AELCode"
  (statement := /-- The AEL construction takes an $(n, d, \lambda)$-expander $G$ (\cref{def:ExpanderGraph}) on left and right vertex sets $L = R = \{0, \dots, n-1\}$, an outer code $C_{\mathrm{out}} \subseteq \Sigma^{n}$ of block length $n$, an inner code $C_{\mathrm{in}} \subseteq \Sigma^{d}$, and an inner encoding map $\mathrm{Enc} : \Sigma \to \Sigma^{d}$ with $\mathrm{Enc}(a) \in C_{\mathrm{in}}$ for every $a \in \Sigma$, and produces the AEL code $C_{\mathrm{AEL}} \subseteq (\Sigma^{d})^{n}$ as follows. The inner encoding map $\mathrm{Enc}$ is injective: distinct symbols $a \neq a'$ in $\Sigma$ satisfy $\mathrm{Enc}(a) \neq \mathrm{Enc}(a')$. This is intrinsic to the AEL construction, in which $\mathrm{Enc}$ is the encoding map of the inner code $C_{\mathrm{in}}$; it is precisely what makes the AEL code inherit an amplified form of the outer code's distance, since without it two outer codewords far apart could be mapped to AEL codewords that agree on all but a vanishing fraction of coordinates. Fix a port model of $G$: a bijection $\pi$ of $L \times \{0, \dots, d-1\}$ onto $R \times \{0, \dots, d-1\}$ that sends each left port $(\ell, i)$ to a right port whose right vertex $r(\ell, i)$ (the first component of $\pi(\ell, i)$) is a neighbour of $\ell$ in $G$, i.e. $r(\ell, i) \in N(\ell)$, and such that for each fixed $\ell \in L$ the map $i \mapsto r(\ell, i)$ is injective, so it enumerates the $d$ neighbours of $\ell$. Given an outer codeword $c \in C_{\mathrm{out}}$, each coordinate $c_\ell$ is encoded into the block $\mathrm{Enc}(c_\ell) \in \Sigma^{d}$ carried on the left ports $\{(\ell, i)\}_{i}$, and these symbols are redistributed along $\pi$ so that each right vertex $r$ collects in its port $j$ the symbol on the left port $\pi^{-1}(r, j)$: writing $(\ell', i') = \pi^{-1}(r, j)$, the resulting word satisfies $C_{\mathrm{AEL}}(c)_{r, j} = \mathrm{Enc}(c_{\ell'})_{i'}$, and $C_{\mathrm{AEL}}$ is the image of $C_{\mathrm{out}}$ under $c \mapsto C_{\mathrm{AEL}}(c)$. Finally, $C_{\mathrm{out}}$ has relative distance at least $\delta_{\mathrm{out}}$: any two distinct codewords $x, y \in C_{\mathrm{out}}$ satisfy $\frac{1}{n}\,\bigl\lvert\{\, i : x_i \neq y_i \,\}\bigr\rvert \ge \delta_{\mathrm{out}}$. -/)
  (title := /-- AEL code from an expander, outer code, and inner code -/)
  (latexEnv := "definition")]
structure AELCode (n d : ℕ) (lam δout : ℝ) (α : Type*) [DecidableEq α] where
  G : ExpanderGraph n d lam
  outer : Set (Fin n → α)
  inner : Set (Fin d → α)
  code : Set (Fin n → (Fin d → α))
  innerEnc : α → (Fin d → α)
  hEncMem : ∀ a : α, innerEnc a ∈ inner
  hEncInj : Function.Injective innerEnc
  edge : (Fin n × Fin d) ≃ (Fin n × Fin d)
  hEdgeMem : ∀ (ℓ : Fin n) (i : Fin d), (edge (ℓ, i)).1 ∈ G.nbrs ℓ
  hEdgeInj : ∀ ℓ : Fin n, Function.Injective (fun i : Fin d => (edge (ℓ, i)).1)
  hCode : code =
      (fun c : Fin n → α =>
        fun r : Fin n => fun j : Fin d =>
          innerEnc (c (edge.symm (r, j)).1) ((edge.symm (r, j)).2)) '' outer
  hOuterDist : ∀ x ∈ outer, ∀ y ∈ outer, x ≠ y →
      δout ≤ ((Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card : ℝ) / (n : ℝ)

@[blueprint "lem:base-case-avg-ldc"
  (statement := /-- Let $\delta, \varepsilon \in \mathbb{R}$, let $\widetilde{g} : \{0,\dots,n-1\} \to \Sigma \cup \{\bot\}$ be a partially erased word with erasure fraction $s = s(\widetilde{g})$ as in \cref{def:erasureFrac}, and let $\mathcal{H}$ be a finite set of words in $\Sigma^n$ with $1 \le \lvert \mathcal{H}\rvert \le 1$, i.e. $\lvert \mathcal{H}\rvert = 1$. Then $$(\lvert \mathcal{H}\rvert - 1)\,(\delta - s - \varepsilon) \le \sum_{h \in \mathcal{H}} \Delta(\widetilde{g}, h),$$ where $\Delta$ is the erasure distance of \cref{def:erasureDist}. -/)
  (proof := /-- The two bounds $1 \le \lvert \mathcal{H}\rvert$ and $\lvert \mathcal{H}\rvert \le 1$ force $\lvert \mathcal{H}\rvert = 1$, so $\lvert \mathcal{H}\rvert - 1 = 0$ and the left-hand side is $0$. The right-hand side is $\Delta(\widetilde{g}, h_0)$ for the unique $h_0 \in \mathcal{H}$, which by \cref{def:erasureDist} is a nonnegative fraction of coordinates; hence $0 \le \Delta(\widetilde{g}, h_0)$ and the inequality holds. This is exactly the base case $\lvert \mathcal{H}\rvert = 1$ of the induction on list size in \cref{def:AvgRadiusLDCErasures}, whose defining inequality quantifies only over nonempty lists. -/)
  (title := /-- Base case: lists of size at most one -/)
  (latexEnv := "lemma")]
lemma base_case_avg_ldc {n : ℕ} {α : Type*} [DecidableEq α]
    (δ ε : ℝ) (g : Fin n → Option α) (H : Finset (Fin n → α))
    (hne : 1 ≤ H.card) (hcard : H.card ≤ 1) :
    ((H.card : ℝ) - 1) * (δ - erasureFrac g - ε) ≤ ∑ h ∈ H, erasureDist g h := by
  have hc1 : H.card = 1 := le_antisymm hcard hne
  rw [hc1]
  simp only [Nat.cast_one, sub_self, zero_mul]
  apply Finset.sum_nonneg
  intro h _
  unfold erasureDist
  positivity

@[blueprint "lem:sampling-erasure"
  (statement := /-- Let $G$ be an $(n, d, \lambda)$-expander with $n, d \ge 1$, let $k \ge 1$ and $\delta_{\mathrm{out}} > 0$, and suppose $\lambda \le \frac{\delta_{\mathrm{out}}}{k^{k}} \cdot \frac{\varepsilon}{6}$. Let $S \subseteq R$ be a set of right vertices with $s = \frac{\lvert S\rvert}{n}$, and let $L^* \subseteq L$ satisfy $\lvert L^*\rvert \ge \frac{\delta_{\mathrm{out}}\, n}{k^{k}}$. Writing $s_\ell = \frac{\lvert N(\ell) \cap S\rvert}{d}$ for the local erasure fraction at $\ell$, we have $\frac{1}{\lvert L^*\rvert} \sum_{\ell \in L^*} s_\ell \le s + \frac{\varepsilon}{6}$. -/)
  (proof := /-- Applying the expander mixing inequality of \cref{def:ExpanderGraph} to the sets $L^*$ and $S$ gives $\sum_{\ell \in L^*} \lvert N(\ell) \cap S\rvert = E(L^*, S) \le \frac{d}{n}\,\lvert L^*\rvert\,\lvert S\rvert + \lambda\, d\, n$. Dividing through by $d\,\lvert L^*\rvert$ yields $\frac{1}{\lvert L^*\rvert} \sum_{\ell \in L^*} s_\ell \le \frac{\lvert S\rvert}{n} + \frac{\lambda\, n}{\lvert L^*\rvert} = s + \frac{\lambda\, n}{\lvert L^*\rvert}$. Finally, $\lvert L^*\rvert \ge \delta_{\mathrm{out}}\, n / k^{k}$ and $\lambda \le (\delta_{\mathrm{out}} / k^{k})\,(\varepsilon / 6)$ give $\frac{\lambda\, n}{\lvert L^*\rvert} \le \frac{\varepsilon}{6}$, whence $\frac{1}{\lvert L^*\rvert} \sum_{\ell \in L^*} s_\ell \le s + \frac{\varepsilon}{6}$. -/)
  (title := /-- Sampling bound for local erasure fractions -/)
  (latexEnv := "lemma")]
lemma sampling_erasure {n d k : ℕ} {lam δout ε : ℝ}
    (G : ExpanderGraph n d lam) (Lstar S : Finset (Fin n))
    (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) (hδout : 0 < δout)
    (hLstar : δout * (n : ℝ) / (k : ℝ) ^ k ≤ (Lstar.card : ℝ))
    (hlam : lam ≤ δout / (k : ℝ) ^ k * (ε / 6)) :
    (∑ ℓ ∈ Lstar, ((G.nbrs ℓ ∩ S).card : ℝ) / (d : ℝ)) / (Lstar.card : ℝ)
      ≤ (S.card : ℝ) / (n : ℝ) + ε / 6 := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hKK0 : (0:ℝ) < (k:ℝ)^k := pow_pos hkr k
  have hLc0 : (0:ℝ) < (Lstar.card : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos hδout hn0) hKK0) hLstar
  have hlam0 : (0:ℝ) ≤ lam := by
    have hmix := G.mixing ∅ ∅
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
      zero_mul, sub_zero, abs_zero] at hmix
    nlinarith [hmix, mul_pos hd0 hn0]
  have hε6 : (0:ℝ) ≤ ε / 6 := by
    have h1 : (0:ℝ) ≤ δout / (k:ℝ)^k * (ε / 6) := le_trans hlam0 hlam
    have hdiv : (0:ℝ) < δout / (k:ℝ)^k := div_pos hδout hKK0
    nlinarith [h1, hdiv]
  have hkey : lam * (n:ℝ) ≤ ε / 6 * (Lstar.card:ℝ) := by
    have step1 : lam * (n:ℝ) ≤ (δout / (k:ℝ)^k * (ε / 6)) * (n:ℝ) :=
      mul_le_mul_of_nonneg_right hlam (le_of_lt hn0)
    have step2 : (δout / (k:ℝ)^k * (ε / 6)) * (n:ℝ) ≤ ε / 6 * (Lstar.card:ℝ) := by
      have h2 : ε / 6 * (δout * (n:ℝ) / (k:ℝ)^k) ≤ ε / 6 * (Lstar.card:ℝ) :=
        mul_le_mul_of_nonneg_left hLstar hε6
      have heq : (δout / (k:ℝ)^k * (ε / 6)) * (n:ℝ)
          = ε / 6 * (δout * (n:ℝ) / (k:ℝ)^k) := by ring
      rw [heq]; exact h2
    linarith [step1, step2]
  have hkey2 : lam * (n:ℝ) * (d:ℝ) ≤ ε / 6 * (Lstar.card:ℝ) * (d:ℝ) :=
    mul_le_mul_of_nonneg_right hkey (le_of_lt hd0)
  have hSum : (∑ ℓ ∈ Lstar, ((G.nbrs ℓ ∩ S).card:ℝ))
      ≤ (d:ℝ) / (n:ℝ) * (Lstar.card:ℝ) * (S.card:ℝ) + lam * (d:ℝ) * (n:ℝ) := by
    have h := (abs_le.mp (G.mixing Lstar S)).2
    linarith [h]
  have hprod : (0:ℝ) < (d:ℝ) * (Lstar.card:ℝ) := mul_pos hd0 hLc0
  have hfinal : (∑ ℓ ∈ Lstar, ((G.nbrs ℓ ∩ S).card:ℝ))
      ≤ ((S.card:ℝ) / (n:ℝ) + ε / 6) * ((d:ℝ) * (Lstar.card:ℝ)) := by
    have hexp : ((S.card:ℝ) / (n:ℝ) + ε / 6) * ((d:ℝ) * (Lstar.card:ℝ))
        = (d:ℝ) / (n:ℝ) * (Lstar.card:ℝ) * (S.card:ℝ)
            + ε / 6 * ((d:ℝ) * (Lstar.card:ℝ)) := by ring
    have hcmp : lam * (d:ℝ) * (n:ℝ) ≤ ε / 6 * ((d:ℝ) * (Lstar.card:ℝ)) := by
      nlinarith [hkey2]
    rw [hexp]
    linarith [hSum, hcmp]
  rw [← Finset.sum_div, div_div, div_le_iff₀ hprod]
  exact hfinal

@[blueprint "lem:local-distance-bound"
  (statement := /-- Let $C_{\mathrm{in}} \subseteq \Sigma_{\mathrm{in}}^{d}$ be $(\delta_0, k_0, \varepsilon/2)$ average-radius list decodable with erasures. Let $\widetilde{g}_\ell$ be a partially erased word over the inner block, with local erasure fraction $s_\ell = s(\widetilde{g}_\ell)$, and let $\{f_{j,\ell}\}_{j \in [p]} \subseteq C_{\mathrm{in}}$ be a nonempty list of $1 \le p \le k_0$ inner codewords. Then $\sum_{j \in [p]} \Delta(\widetilde{g}_\ell, f_{j,\ell}) \ge (p - 1)\,(\delta_0 - s_\ell - \tfrac{\varepsilon}{2})$. -/)
  (proof := /-- The family $\{f_{j,\ell}\}_{j \in [p]}$ is a nonempty list of $1 \le p \le k_0$ codewords of $C_{\mathrm{in}}$. Since $C_{\mathrm{in}}$ is $(\delta_0, k_0, \varepsilon/2)$ average-radius list decodable with erasures, the defining inequality of \cref{def:AvgRadiusLDCErasures}, applied to the partially erased word $\widetilde{g}_\ell$ and this nonempty list, gives $\sum_{j \in [p]} \Delta(\widetilde{g}_\ell, f_{j,\ell}) \ge (p - 1)\,(\delta_0 - s(\widetilde{g}_\ell) - \tfrac{\varepsilon}{2}) = (p - 1)\,(\delta_0 - s_\ell - \tfrac{\varepsilon}{2})$. -/)
  (title := /-- Local distance bound from inner-code decodability -/)
  (latexEnv := "lemma")]
lemma local_distance_bound {d k0 : ℕ} {δ0 ε : ℝ} {α : Type*} [DecidableEq α]
    (Cinn : Set (Fin d → α))
    (hinner : AvgRadiusLDCErasures Cinn δ0 k0 (ε / 2))
    (gloc : Fin d → Option α) (F : Finset (Fin d → α))
    (hF : (↑F : Set (Fin d → α)) ⊆ Cinn) (hne : 1 ≤ F.card) (hp : F.card ≤ k0) :
    ((F.card : ℝ) - 1) * (δ0 - erasureFrac gloc - ε / 2)
      ≤ ∑ f ∈ F, erasureDist gloc f := by
  exact hinner gloc F hF hne hp

@[blueprint "lem:inductive-part-bound"
  (statement := /-- Suppose the AEL code $C_{\mathrm{AEL}}$, built on an $(n, d, \lambda)$-expander $G$ with $n, d \ge 1$, $\delta_{\mathrm{out}} > 0$, $k \ge 1$, and $\lambda \le \frac{\delta_{\mathrm{out}}}{k^{k}} \cdot \frac{\varepsilon}{6}$, is $(\delta_0, k - 1, \varepsilon)$ average-radius list decodable with erasures. Fix a port model $\pi$ of $G$: a bijection of left ports $L \times \{0,\dots,d-1\}$ onto right ports $R \times \{0,\dots,d-1\}$ sending each left port $(\ell, i)$ to a right port whose right vertex $r(\ell, i)$ satisfies $r(\ell, i) \in N(\ell)$, and with $i \mapsto r(\ell, i)$ injective for each fixed $\ell$. Let $\widetilde{g}$ be a partially erased word over $R$ (whole right-vertex blocks in $\Sigma^{d}$, possibly erased) with erasure fraction $s = s(\widetilde{g})$, let $L^* \subseteq L$ satisfy $\lvert L^*\rvert \ge \frac{\delta_{\mathrm{out}}\, n}{k^{k}}$, and let $\mathcal{H}_j \subseteq C_{\mathrm{AEL}}$ be a nonempty part of the list with $1 \le \lvert \mathcal{H}_j\rvert \le k - 1$. For each $\ell$ let $\widetilde{g}_\ell$ be the induced local word, defined portwise by $(\widetilde{g}_\ell)_i = (\widetilde{g}_{r(\ell, i)})_{j(\ell, i)}$ read at the matched port coordinate (an erasure exactly when the block $\widetilde{g}_{r(\ell, i)}$ is erased), and let $f_{j,\ell}$ be the common local codeword of $\mathcal{H}_j$, characterised by $(f_{j,\ell})_i = h_{r(\ell, i)}$ at that port coordinate for every $h \in \mathcal{H}_j$ (well defined since all $h \in \mathcal{H}_j$ share the same local block at $\ell$). Then $$(\lvert \mathcal{H}_j\rvert - 1)\,(\delta_0 - s - \varepsilon) + \frac{1}{\lvert L^*\rvert}\sum_{\ell \in L^*} \Delta(\widetilde{g}_\ell, f_{j,\ell}) - \frac{\varepsilon}{6} \le \sum_{h \in \mathcal{H}_j} \Delta_R(\widetilde{g}, h).$$ -/)
  (proof := /-- By definition of the common local codeword, $h_\ell = f_{j,\ell}$ for all $h \in \mathcal{H}_j$ and all $\ell \in L^*$; hence whenever $\widetilde{g}_\ell$ and $f_{j,\ell}$ disagree on an unerased edge $(\ell, r)$, the right vertex $r$ is a common error location for every $h \in \mathcal{H}_j$. Let $S_j = \{\, r \in R : \widetilde{g}_r \neq \bot \text{ and } (\widetilde{g}_\ell)_{(\ell,r)} \neq (f_{j,\ell})_{(\ell,r)} \text{ for some } \ell \in L^* \,\}$ and $s_j = \lvert S_j\rvert / n$. Let $\widetilde{g}^{(j)}$ be obtained from $\widetilde{g}$ by erasing every coordinate in $S_j$; then $\Delta_R(\widetilde{g}^{(j)}, h) = \Delta_R(\widetilde{g}, h) - s_j$ for all $h \in \mathcal{H}_j$. Applying the hypothesis that $C_{\mathrm{AEL}}$ is $(\delta_0, k - 1, \varepsilon)$ average-radius list decodable with erasures, in the sense of \cref{def:AvgRadiusLDCErasures}, to $\widetilde{g}^{(j)}$ and $\mathcal{H}_j$ gives $\sum_{h \in \mathcal{H}_j} (\Delta_R(\widetilde{g}, h) - s_j) \ge (\lvert \mathcal{H}_j\rvert - 1)\,(\delta_0 - s - s_j - \varepsilon)$, hence $\sum_{h \in \mathcal{H}_j} \Delta_R(\widetilde{g}, h) \ge (\lvert \mathcal{H}_j\rvert - 1)\,(\delta_0 - s - \varepsilon) + s_j$. To bound $s_j$ from below, fix $\ell \in L^*$; since $\widetilde{g}_\ell$ is erased exactly on the ports whose right block is erased, every port $i$ with $(\widetilde{g}_\ell)_i \neq \bot$ and $(\widetilde{g}_\ell)_i \neq (f_{j,\ell})_i$ has right vertex $r(\ell, i) \in N(\ell) \cap S_j$, and since $i \mapsto r(\ell, i)$ is injective this yields $\Delta(\widetilde{g}_\ell, f_{j,\ell}) \le \lvert N(\ell) \cap S_j\rvert / d$. Averaging over $\ell \in L^*$ and applying the sampling bound of \cref{lem:sampling-erasure} to $L^*$ and $S_j$ gives $\frac{1}{\lvert L^*\rvert}\sum_{\ell \in L^*} \Delta(\widetilde{g}_\ell, f_{j,\ell}) \le \frac{1}{\lvert L^*\rvert}\sum_{\ell \in L^*} \frac{\lvert N(\ell) \cap S_j\rvert}{d} \le \frac{\lvert S_j\rvert}{n} + \frac{\varepsilon}{6} = s_j + \frac{\varepsilon}{6}$. Therefore $s_j \ge \frac{1}{\lvert L^*\rvert}\sum_{\ell \in L^*} \Delta(\widetilde{g}_\ell, f_{j,\ell}) - \frac{\varepsilon}{6}$, and substituting into the previous bound yields the claim. -/)
  (title := /-- Inductive bound on distances over a single part -/)
  (latexEnv := "lemma")]
lemma inductive_part_bound {n d k : ℕ} {lam δ0 δout ε : ℝ} {α : Type*} [DecidableEq α]
    (G : ExpanderGraph n d lam)
    (code : Set (Fin n → (Fin d → α)))
    (received : Fin n → Option (Fin d → α))
    (Hj : Finset (Fin n → (Fin d → α)))
    (Lstar : Finset (Fin n))
    (gloc : Fin n → (Fin d → Option α))
    (fj : Fin n → (Fin d → α))
    (edge : (Fin n × Fin d) ≃ (Fin n × Fin d))
    (hn : 0 < n) (hd : 0 < d) (hk : 1 ≤ k) (hδout : 0 < δout)
    (hIH : AvgRadiusLDCErasures code δ0 (k - 1) ε)
    (hHj : (↑Hj : Set (Fin n → (Fin d → α))) ⊆ code)
    (hHjne : 1 ≤ Hj.card) (hHjcard : Hj.card ≤ k - 1)
    (hEdgeMem : ∀ (ℓ : Fin n) (i : Fin d), (edge (ℓ, i)).1 ∈ G.nbrs ℓ)
    (hEdgeInj : ∀ ℓ : Fin n, Function.Injective (fun i : Fin d => (edge (ℓ, i)).1))
    (hgloc : ∀ (ℓ : Fin n) (i : Fin d),
      gloc ℓ i = Option.map (fun w : Fin d → α => w (edge (ℓ, i)).2) (received (edge (ℓ, i)).1))
    (hfj : ∀ h ∈ Hj, ∀ (ℓ : Fin n) (i : Fin d),
      fj ℓ i = h (edge (ℓ, i)).1 (edge (ℓ, i)).2)
    (hLstar : δout * (n : ℝ) / (k : ℝ) ^ k ≤ (Lstar.card : ℝ))
    (hlam : lam ≤ δout / (k : ℝ) ^ k * (ε / 6)) :
    ((Hj.card : ℝ) - 1) * (δ0 - erasureFrac received - ε)
        + (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)) / (Lstar.card : ℝ) - ε / 6
      ≤ ∑ h ∈ Hj, erasureDist received h := by
  classical
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hkr : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hKK0 : (0:ℝ) < (k:ℝ) ^ k := pow_pos hkr k
  have hLc0 : (0:ℝ) < (Lstar.card : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos hδout hn0) hKK0) hLstar
  set Sj : Finset (Fin n) :=
    Finset.univ.filter (fun r => received r ≠ none ∧
      ∃ ℓ ∈ Lstar, ∃ i : Fin d, (edge (ℓ, i)).1 = r ∧ gloc ℓ i ≠ some (fj ℓ i))
    with hSj
  have hmemSj : ∀ r : Fin n, r ∈ Sj ↔ received r ≠ none ∧
      ∃ ℓ ∈ Lstar, ∃ i : Fin d, (edge (ℓ, i)).1 = r ∧ gloc ℓ i ≠ some (fj ℓ i) := by
    intro r
    rw [hSj, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ r, h⟩⟩
  set received' : Fin n → Option (Fin d → α) :=
    fun r => if r ∈ Sj then none else received r with hrecv'
  have hSj_err : ∀ h ∈ Hj, ∀ r ∈ Sj, received r ≠ none ∧ received r ≠ some (h r) := by
    intro h hh r hr
    rw [hmemSj] at hr
    obtain ⟨hne, ℓ, hℓ, i, heq, hdis⟩ := hr
    refine ⟨hne, ?_⟩
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
    have hgi : gloc ℓ i = some (w (edge (ℓ, i)).2) := by
      rw [hgloc ℓ i, heq, hw, Option.map_some]
    rw [hgi] at hdis
    have hne2 : w (edge (ℓ, i)).2 ≠ fj ℓ i := fun hc => hdis (by rw [hc])
    have hfjval : fj ℓ i = h r (edge (ℓ, i)).2 := by rw [hfj h hh ℓ i, heq]
    rw [hw]
    intro hcontra
    have hwh : w = h r := Option.some_inj.mp hcontra
    apply hne2
    rw [hwh, hfjval]
  have hdistB : ∀ h ∈ Hj,
      erasureDist received' h = erasureDist received h - (Sj.card : ℝ) / (n : ℝ) := by
    intro h hh
    have hsub : Sj ⊆ Finset.univ.filter
        (fun r => received r ≠ none ∧ received r ≠ some (h r)) := by
      intro r hr
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ r, hSj_err h hh r hr⟩
    have hset : Finset.univ.filter (fun r => received' r ≠ none ∧ received' r ≠ some (h r))
        = (Finset.univ.filter (fun r => received r ≠ none ∧ received r ≠ some (h r))) \ Sj := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩
        have hrni : r ∉ Sj := by
          intro hmem
          have hnone : received' r = none := by rw [hrecv']; simp [hmem]
          exact h1 hnone
        have hval : received' r = received r := by rw [hrecv']; simp [hrni]
        rw [hval] at h1 h2
        exact ⟨⟨h1, h2⟩, hrni⟩
      · rintro ⟨⟨h1, h2⟩, hrni⟩
        have hval : received' r = received r := by rw [hrecv']; simp [hrni]
        rw [hval]
        exact ⟨h1, h2⟩
    simp only [erasureDist]
    rw [hset, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    ring
  have hfracA : erasureFrac received' = erasureFrac received + (Sj.card : ℝ) / (n : ℝ) := by
    have hset : Finset.univ.filter (fun r => received' r = none)
        = Sj ∪ Finset.univ.filter (fun r => received r = none) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hmem : r ∈ Sj
      · rw [hrecv']; simp [hmem]
      · rw [hrecv']; simp [hmem]
    have hdisj : Disjoint Sj (Finset.univ.filter (fun r => received r = none)) := by
      rw [Finset.disjoint_left]
      intro r hrSj hrE
      rw [Finset.mem_filter] at hrE
      exact ((hmemSj r).mp hrSj).1 hrE.2
    simp only [erasureFrac]
    rw [hset, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
    ring
  have hsumB : ∑ h ∈ Hj, erasureDist received' h
      = (∑ h ∈ Hj, erasureDist received h) - (Hj.card : ℝ) * ((Sj.card : ℝ) / (n : ℝ)) := by
    rw [Finset.sum_congr rfl (fun h hh => hdistB h hh),
        Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have F1 : (↑Hj.card - 1) * (δ0 - erasureFrac received - ε) + (Sj.card : ℝ) / (n : ℝ)
      ≤ ∑ h ∈ Hj, erasureDist received h := by
    have hih : (↑Hj.card - 1) * (δ0 - erasureFrac received' - ε)
        ≤ ∑ h ∈ Hj, erasureDist received' h := hIH received' Hj hHj hHjne hHjcard
    rw [hfracA, hsumB] at hih
    have hkey : (↑Hj.card - 1) * (δ0 - (erasureFrac received + (Sj.card : ℝ) / (n : ℝ)) - ε)
        = (↑Hj.card - 1) * (δ0 - erasureFrac received - ε)
          - (↑Hj.card - 1) * ((Sj.card : ℝ) / (n : ℝ)) := by ring
    have hmul : (↑Hj.card - 1) * ((Sj.card : ℝ) / (n : ℝ))
        = (↑Hj.card) * ((Sj.card : ℝ) / (n : ℝ)) - ((Sj.card : ℝ) / (n : ℝ)) := by ring
    rw [hkey] at hih
    linarith [hih, hmul]
  have F2 : (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)) / (Lstar.card : ℝ) - ε / 6
      ≤ (Sj.card : ℝ) / (n : ℝ) := by
    have hpt : ∀ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)
        ≤ ((G.nbrs ℓ ∩ Sj).card : ℝ) / (d : ℝ) := by
      intro ℓ hℓ
      have hcard : (Finset.univ.filter
          (fun i : Fin d => gloc ℓ i ≠ none ∧ gloc ℓ i ≠ some (fj ℓ i))).card
          ≤ (G.nbrs ℓ ∩ Sj).card := by
        have himg : (Finset.univ.filter
            (fun i : Fin d => gloc ℓ i ≠ none ∧ gloc ℓ i ≠ some (fj ℓ i))).image
              (fun i : Fin d => (edge (ℓ, i)).1) ⊆ G.nbrs ℓ ∩ Sj := by
          intro r hr
          rw [Finset.mem_image] at hr
          obtain ⟨i, hiP, hir⟩ := hr
          rw [Finset.mem_filter] at hiP
          obtain ⟨-, hi1, hi2⟩ := hiP
          rw [Finset.mem_inter]
          refine ⟨?_, ?_⟩
          · rw [← hir]; exact hEdgeMem ℓ i
          · rw [hmemSj, ← hir]
            refine ⟨?_, ℓ, hℓ, i, rfl, hi2⟩
            intro hcontra
            apply hi1
            rw [hgloc ℓ i, hcontra, Option.map_none]
        calc (Finset.univ.filter
                (fun i : Fin d => gloc ℓ i ≠ none ∧ gloc ℓ i ≠ some (fj ℓ i))).card
            = ((Finset.univ.filter
                (fun i : Fin d => gloc ℓ i ≠ none ∧ gloc ℓ i ≠ some (fj ℓ i))).image
                (fun i : Fin d => (edge (ℓ, i)).1)).card :=
              (Finset.card_image_of_injective _ (hEdgeInj ℓ)).symm
          _ ≤ (G.nbrs ℓ ∩ Sj).card := Finset.card_le_card himg
      simp only [erasureDist]
      gcongr
    have hsum_le : ∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)
        ≤ ∑ ℓ ∈ Lstar, ((G.nbrs ℓ ∩ Sj).card : ℝ) / (d : ℝ) :=
      Finset.sum_le_sum hpt
    have hsamp := sampling_erasure G Lstar Sj hn hd hk hδout hLstar hlam
    have hdiv : (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)) / (Lstar.card : ℝ)
        ≤ (∑ ℓ ∈ Lstar, ((G.nbrs ℓ ∩ Sj).card : ℝ) / (d : ℝ)) / (Lstar.card : ℝ) := by
      gcongr
    linarith [hdiv, hsamp]
  linarith [F1, F2]

@[blueprint "lem:local-sampling-bound"
  (statement := /-- Let $G$ be an $(n, d, \lambda)$-expander with $n, d \ge 1$, let $k \ge 1$ and $\varepsilon > 0$. Let $S \subseteq R$ be a set of right vertices with $s = \frac{\lvert S\rvert}{n}$, and let $L^* \subseteq L$ be a nonempty set of left vertices ($\lvert L^*\rvert > 0$) satisfying both $\frac{\delta_{\mathrm{out}}\, n}{k^{k}} \le \lvert L^*\rvert$ and $\lambda \le \frac{\delta_{\mathrm{out}}}{k^{k}} \cdot \frac{\varepsilon}{6}$. Writing $s_\ell = \frac{\lvert N(\ell) \cap S\rvert}{d}$ for the local erasure fraction at $\ell$, we have $\frac{1}{\lvert L^*\rvert} \sum_{\ell \in L^*} s_\ell \le s + \frac{\varepsilon}{6}$. -/)
  (proof := /-- If $\delta_{\mathrm{out}}>0$, the conclusion follows directly from \cref{lem:sampling-erasure}. Suppose instead that $\delta_{\mathrm{out}}\leq 0$. Applying the expander mixing inequality of \cref{def:ExpanderGraph} to the two empty sets, and using $n,d>0$, gives $\lambda\geq 0$. On the other hand, $\varepsilon/6\geq 0$ and $k^k>0$, so the assumed spectral bound gives $\lambda\leq 0$; hence $\lambda=0$. Define $\delta_{\mathrm{aux}}=\lvert L^*\rvert k^k/n$. The positivity of $\lvert L^*\rvert$, $k$, and $n$ gives $\delta_{\mathrm{aux}}>0$, while $\delta_{\mathrm{aux}}n/k^k=\lvert L^*\rvert$ and $\lambda=0\leq (\delta_{\mathrm{aux}}/k^k)(\varepsilon/6)$. Applying \cref{lem:sampling-erasure} with $\delta_{\mathrm{aux}}$ in place of $\delta_{\mathrm{out}}$ therefore yields $\frac{1}{\lvert L^*\rvert}\sum_{\ell\in L^*}s_\ell\leq \frac{\lvert S\rvert}{n}+\frac{\varepsilon}{6}$, as required. -/)
  (title := /-- Sampling bound for local erasure fractions, parametrised by a nonempty left set -/)
  (latexEnv := "lemma")]
lemma local_sampling_bound {n d k : ℕ} {lam δout ε : ℝ}
    (G : ExpanderGraph n d lam) (Lstar S : Finset (Fin n))
    (hn : 0 < n) (hd : 0 < d) (hk : 0 < k) (hε : 0 < ε)
    (hLc0 : (0:ℝ) < (Lstar.card : ℝ))
    (hLstar : δout * (n : ℝ) / (k : ℝ) ^ k ≤ (Lstar.card : ℝ))
    (hlam : lam ≤ δout / (k : ℝ) ^ k * (ε / 6)) :
    (∑ ℓ ∈ Lstar, ((G.nbrs ℓ ∩ S).card : ℝ) / (d : ℝ)) / (Lstar.card : ℝ)
      ≤ (S.card : ℝ) / (n : ℝ) + ε / 6 := by
  by_cases hδ : 0 < δout
  · exact sampling_erasure G Lstar S hn hd hk hδ hLstar hlam
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hpow : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hk0 k
    have hlam0 : (0 : ℝ) ≤ lam := by
      have hmix := G.mixing ∅ ∅
      simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
        zero_mul, sub_zero, abs_zero] at hmix
      nlinarith [hmix, mul_pos hd0 hn0]
    have hε6 : (0 : ℝ) ≤ ε / 6 := by linarith
    have hδnonpos : δout ≤ 0 := le_of_not_gt hδ
    have hright : δout / (k : ℝ) ^ k * (ε / 6) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg hδnonpos (le_of_lt hpow)) hε6
    have hlam_eq : lam = 0 := le_antisymm (hlam.trans hright) hlam0
    let δaux : ℝ := (Lstar.card : ℝ) * (k : ℝ) ^ k / (n : ℝ)
    have hδaux : 0 < δaux := div_pos (mul_pos hLc0 hpow) hn0
    have hsize : δaux * (n : ℝ) / (k : ℝ) ^ k = (Lstar.card : ℝ) := by
      dsimp [δaux]
      field_simp [ne_of_gt hn0, ne_of_gt hpow]
    have hlamaux : lam ≤ δaux / (k : ℝ) ^ k * (ε / 6) := by
      rw [hlam_eq]
      positivity
    exact sampling_erasure G Lstar S hn hd hk hδaux (le_of_eq hsize) hlamaux

@[blueprint "lem:local-inductive-part-bound"
  (statement := /-- Let $C$ be a code on the right vertices of an $(n,d,\lambda)$-expander, where $n,d\geq 1$. Fix an integer $k\geq 1$, a nonempty set $L^*$ of left vertices satisfying $\delta_{\mathrm{out}}n/k^k\leq |L^*|$, and assume $\lambda\leq \delta_{\mathrm{out}}\varepsilon/(6k^k)$. Suppose that $C$ is $(\delta_0,k-1,\varepsilon)$ average-radius list decodable with erasures. If a nonempty list $H_j\subseteq C$ has at most $k-1$ elements and all its words induce the same local codeword $f_{j,\ell}$ at every $\ell\in L^*$, then its global distance sum is at least $(|H_j|-1)(\delta_0-s-\varepsilon)$ plus the average local distance from the induced received words to $f_{j,\ell}$, minus $\varepsilon/6$. -/)
  (proof := /-- If $\delta_{\mathrm{out}}>0$ and $H_j$ is a singleton, extend its common local codeword from $L^*$ to every left vertex using the unique word in $H_j$; \cref{lem:inductive-part-bound} then gives the claim, since the extended local codeword agrees with the prescribed one on $L^*$. In all remaining cases, erase every right vertex at which some local comparison on $L^*$ detects an unerased disagreement with the common local codeword. Every resulting new erasure was a disagreement for every word of $H_j$, because the words have the prescribed common local codeword on $L^*$. Applying the inductive average-radius hypothesis to this additionally erased received word yields the global lower bound with an additive term equal to the density of newly erased vertices. Each local disagreement maps injectively into this new-erasure set inside the corresponding neighbourhood. Averaging this pointwise comparison and applying \cref{lem:local-sampling-bound} shows that the new-erasure density is at least the average local distance minus $\varepsilon/6$, which gives the claim. -/)
  (title := /-- Inductive distance bound for a part agreeing on a nonempty left set -/)
  (latexEnv := "lemma")]
lemma local_inductive_part_bound {n d k : ℕ} {lam δ0 δout ε : ℝ}
    {α : Type*} [DecidableEq α]
    (G : ExpanderGraph n d lam)
    (code : Set (Fin n → (Fin d → α)))
    (received : Fin n → Option (Fin d → α))
    (Hj : Finset (Fin n → (Fin d → α)))
    (Lstar : Finset (Fin n))
    (gloc : Fin n → (Fin d → Option α))
    (fj : Fin n → (Fin d → α))
    (edge : (Fin n × Fin d) ≃ (Fin n × Fin d))
    (hn : 0 < n) (hd : 0 < d) (hk : 1 ≤ k) (hε : 0 < ε)
    (hLc0 : (0 : ℝ) < (Lstar.card : ℝ))
    (hIH : AvgRadiusLDCErasures code δ0 (k - 1) ε)
    (hHj : (↑Hj : Set (Fin n → (Fin d → α))) ⊆ code)
    (hHjne : 1 ≤ Hj.card) (hHjcard : Hj.card ≤ k - 1)
    (hEdgeMem : ∀ (ℓ : Fin n) (i : Fin d), (edge (ℓ, i)).1 ∈ G.nbrs ℓ)
    (hEdgeInj : ∀ ℓ : Fin n, Function.Injective (fun i : Fin d => (edge (ℓ, i)).1))
    (hgloc : ∀ (ℓ : Fin n) (i : Fin d),
      gloc ℓ i = Option.map (fun w : Fin d → α => w (edge (ℓ, i)).2)
        (received (edge (ℓ, i)).1))
    (hfj : ∀ h ∈ Hj, ∀ ℓ ∈ Lstar, ∀ i : Fin d,
      fj ℓ i = h (edge (ℓ, i)).1 (edge (ℓ, i)).2)
    (hLstar : δout * (n : ℝ) / (k : ℝ) ^ k ≤ (Lstar.card : ℝ))
    (hlam : lam ≤ δout / (k : ℝ) ^ k * (ε / 6)) :
    ((Hj.card : ℝ) - 1) * (δ0 - erasureFrac received - ε)
        + (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)) / (Lstar.card : ℝ) - ε / 6
      ≤ ∑ h ∈ Hj, erasureDist received h := by
  classical
  have hlegacy_support : 0 < δout ∧ Hj.card ≤ 1 →
      ((Hj.card : ℝ) - 1) * (δ0 - erasureFrac received - ε) +
          (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)) /
            (Lstar.card : ℝ) - ε / 6 ≤
        ∑ h ∈ Hj, erasureDist received h := by
    rintro ⟨hδpos, hcard1⟩
    have hcardeq : Hj.card = 1 := le_antisymm hcard1 hHjne
    obtain ⟨h0, hHj0⟩ := Finset.card_eq_one.mp hcardeq
    have hh0 : h0 ∈ Hj := by rw [hHj0]; exact Finset.mem_singleton_self h0
    let fj' : Fin n → (Fin d → α) := fun ℓ i =>
      h0 (edge (ℓ, i)).1 (edge (ℓ, i)).2
    have hfj' : ∀ h ∈ Hj, ∀ (ℓ : Fin n) (i : Fin d),
        fj' ℓ i = h (edge (ℓ, i)).1 (edge (ℓ, i)).2 := by
      intro h hh ℓ i
      rw [hHj0, Finset.mem_singleton] at hh
      subst h
      rfl
    have hbound := inductive_part_bound G code received Hj Lstar gloc fj' edge
      hn hd hk hδpos hIH hHj hHjne hHjcard hEdgeMem hEdgeInj hgloc hfj'
      hLstar hlam
    have hsum_eq : (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj' ℓ)) =
        ∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ) := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have hfj_eq : fj' ℓ = fj ℓ := by
        funext i
        exact (hfj h0 hh0 ℓ hℓ i).symm
      rw [hfj_eq]
    rw [hsum_eq] at hbound
    exact hbound
  set Sj : Finset (Fin n) :=
    Finset.univ.filter (fun r => received r ≠ none ∧
      ∃ ℓ ∈ Lstar, ∃ i : Fin d, (edge (ℓ, i)).1 = r ∧ gloc ℓ i ≠ some (fj ℓ i))
    with hSj
  have hmemSj : ∀ r : Fin n, r ∈ Sj ↔ received r ≠ none ∧
      ∃ ℓ ∈ Lstar, ∃ i : Fin d, (edge (ℓ, i)).1 = r ∧ gloc ℓ i ≠ some (fj ℓ i) := by
    intro r
    rw [hSj, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ r, h⟩⟩
  set received' : Fin n → Option (Fin d → α) :=
    fun r => if r ∈ Sj then none else received r with hrecv'
  have hSj_err : ∀ h ∈ Hj, ∀ r ∈ Sj,
      received r ≠ none ∧ received r ≠ some (h r) := by
    intro h hh r hr
    rw [hmemSj] at hr
    obtain ⟨hne, ℓ, hℓ, i, heq, hdis⟩ := hr
    refine ⟨hne, ?_⟩
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hne
    have hgi : gloc ℓ i = some (w (edge (ℓ, i)).2) := by
      rw [hgloc ℓ i, heq, hw, Option.map_some]
    rw [hgi] at hdis
    have hne2 : w (edge (ℓ, i)).2 ≠ fj ℓ i := fun hc => hdis (by rw [hc])
    have hfjval : fj ℓ i = h r (edge (ℓ, i)).2 := by
      rw [hfj h hh ℓ hℓ i, heq]
    rw [hw]
    intro hcontra
    have hwh : w = h r := Option.some_inj.mp hcontra
    apply hne2
    rw [hwh, hfjval]
  have hdistB : ∀ h ∈ Hj,
      erasureDist received' h = erasureDist received h - (Sj.card : ℝ) / (n : ℝ) := by
    intro h hh
    have hsub : Sj ⊆ Finset.univ.filter
        (fun r => received r ≠ none ∧ received r ≠ some (h r)) := by
      intro r hr
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ r, hSj_err h hh r hr⟩
    have hset : Finset.univ.filter
        (fun r => received' r ≠ none ∧ received' r ≠ some (h r)) =
        (Finset.univ.filter
          (fun r => received r ≠ none ∧ received r ≠ some (h r))) \ Sj := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · rintro ⟨h1, h2⟩
        have hrni : r ∉ Sj := by
          intro hmem
          have hnone : received' r = none := by rw [hrecv']; simp [hmem]
          exact h1 hnone
        have hval : received' r = received r := by rw [hrecv']; simp [hrni]
        rw [hval] at h1 h2
        exact ⟨⟨h1, h2⟩, hrni⟩
      · rintro ⟨⟨h1, h2⟩, hrni⟩
        have hval : received' r = received r := by rw [hrecv']; simp [hrni]
        rw [hval]
        exact ⟨h1, h2⟩
    simp only [erasureDist]
    rw [hset, Finset.card_sdiff_of_subset hsub,
      Nat.cast_sub (Finset.card_le_card hsub)]
    ring
  have hfracA : erasureFrac received' =
      erasureFrac received + (Sj.card : ℝ) / (n : ℝ) := by
    have hset : Finset.univ.filter (fun r => received' r = none) =
        Sj ∪ Finset.univ.filter (fun r => received r = none) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hmem : r ∈ Sj
      · rw [hrecv']; simp [hmem]
      · rw [hrecv']; simp [hmem]
    have hdisj : Disjoint Sj
        (Finset.univ.filter (fun r => received r = none)) := by
      rw [Finset.disjoint_left]
      intro r hrSj hrE
      rw [Finset.mem_filter] at hrE
      exact ((hmemSj r).mp hrSj).1 hrE.2
    simp only [erasureFrac]
    rw [hset, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
    ring
  have hsumB : ∑ h ∈ Hj, erasureDist received' h =
      (∑ h ∈ Hj, erasureDist received h) -
        (Hj.card : ℝ) * ((Sj.card : ℝ) / (n : ℝ)) := by
    rw [Finset.sum_congr rfl (fun h hh => hdistB h hh),
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have F1 : (↑Hj.card - 1) * (δ0 - erasureFrac received - ε) +
      (Sj.card : ℝ) / (n : ℝ) ≤ ∑ h ∈ Hj, erasureDist received h := by
    have hih : (↑Hj.card - 1) * (δ0 - erasureFrac received' - ε) ≤
        ∑ h ∈ Hj, erasureDist received' h :=
      hIH received' Hj hHj hHjne hHjcard
    rw [hfracA, hsumB] at hih
    have hkey : (↑Hj.card - 1) *
        (δ0 - (erasureFrac received + (Sj.card : ℝ) / (n : ℝ)) - ε) =
        (↑Hj.card - 1) * (δ0 - erasureFrac received - ε) -
          (↑Hj.card - 1) * ((Sj.card : ℝ) / (n : ℝ)) := by ring
    have hmul : (↑Hj.card - 1) * ((Sj.card : ℝ) / (n : ℝ)) =
        (↑Hj.card) * ((Sj.card : ℝ) / (n : ℝ)) -
          ((Sj.card : ℝ) / (n : ℝ)) := by ring
    rw [hkey] at hih
    linarith [hih, hmul]
  have F2 : (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)) /
      (Lstar.card : ℝ) - ε / 6 ≤ (Sj.card : ℝ) / (n : ℝ) := by
    have hpt : ∀ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ) ≤
        ((G.nbrs ℓ ∩ Sj).card : ℝ) / (d : ℝ) := by
      intro ℓ hℓ
      have hcard : (Finset.univ.filter
          (fun i : Fin d => gloc ℓ i ≠ none ∧
            gloc ℓ i ≠ some (fj ℓ i))).card ≤ (G.nbrs ℓ ∩ Sj).card := by
        have himg : (Finset.univ.filter
            (fun i : Fin d => gloc ℓ i ≠ none ∧
              gloc ℓ i ≠ some (fj ℓ i))).image
              (fun i : Fin d => (edge (ℓ, i)).1) ⊆ G.nbrs ℓ ∩ Sj := by
          intro r hr
          rw [Finset.mem_image] at hr
          obtain ⟨i, hiP, hir⟩ := hr
          rw [Finset.mem_filter] at hiP
          obtain ⟨-, hi1, hi2⟩ := hiP
          rw [Finset.mem_inter]
          refine ⟨?_, ?_⟩
          · rw [← hir]
            exact hEdgeMem ℓ i
          · rw [hmemSj, ← hir]
            refine ⟨?_, ℓ, hℓ, i, rfl, hi2⟩
            intro hcontra
            apply hi1
            rw [hgloc ℓ i, hcontra, Option.map_none]
        calc
          (Finset.univ.filter
              (fun i : Fin d => gloc ℓ i ≠ none ∧
                gloc ℓ i ≠ some (fj ℓ i))).card =
              ((Finset.univ.filter
                (fun i : Fin d => gloc ℓ i ≠ none ∧
                  gloc ℓ i ≠ some (fj ℓ i))).image
                    (fun i : Fin d => (edge (ℓ, i)).1)).card :=
            (Finset.card_image_of_injective _ (hEdgeInj ℓ)).symm
          _ ≤ (G.nbrs ℓ ∩ Sj).card := Finset.card_le_card himg
      simp only [erasureDist]
      gcongr
    have hsum_le : ∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ) ≤
        ∑ ℓ ∈ Lstar, ((G.nbrs ℓ ∩ Sj).card : ℝ) / (d : ℝ) :=
      Finset.sum_le_sum hpt
    have hsamp := local_sampling_bound G Lstar Sj hn hd hk hε hLc0 hLstar hlam
    have hdiv : (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (fj ℓ)) /
        (Lstar.card : ℝ) ≤
        (∑ ℓ ∈ Lstar, ((G.nbrs ℓ ∩ Sj).card : ℝ) / (d : ℝ)) /
          (Lstar.card : ℝ) := by
      gcongr
    linarith [hdiv, hsamp]
  by_cases hlegacy : 0 < δout ∧ Hj.card ≤ 1
  · exact hlegacy_support hlegacy
  · linarith [F1, F2]

@[blueprint "lem:local-partition-pigeonhole"
  (statement := /-- Let $H$ be a finite nonempty family and let $v_\ell(h)$ be a finite-valued local view of $h\in H$ at each of $n$ positions. Fix $x,y\in H$, and let $D$ be the nonempty set of positions where $v_\ell(x)\neq v_\ell(y)$. If $\delta n\leq |D|$, then there are a representative map $q:H\to H$ and a nonempty set $L^*$ of positions such that $\delta n/|H|^{|H|}\leq |L^*|$, and, for every $\ell\in L^*$, one has $q(h)=q(h')$ if and only if $v_\ell(h)=v_\ell(h')$. Moreover $q(H)$ has at least two elements. -/)
  (proof := /-- For each position $\ell$, choose canonically, for every $h\in H$, one representative having the same local view as $h$. Equality of representatives is then equivalent to equality of local views. There are exactly $|H|^{|H|}$ functions from $H$ to itself. Among the representative maps occurring on $D$, choose one whose fibre has maximum cardinality and let $L^*$ be that fibre. The finite max-fibre inequality gives $|D|\leq |L^*|\,|H|^{|H|}$; division by the positive number $|H|^{|H|}$ and the assumed lower bound for $|D|$ yield the claimed size of $L^*$. Since $L^*$ is nonempty and contained in $D$, the chosen map sends $x$ and $y$ to distinct representatives, so its image has at least two elements. -/)
  (title := /-- Pigeonhole extraction of a large constant local-view partition -/)
  (latexEnv := "lemma")]
lemma local_partition_pigeonhole {n : ℕ} {δ : ℝ} {β γ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq γ]
    (view : Fin n → β → γ) (x y : β) (hβ : Nonempty β)
    (hDne : (Finset.univ.filter (fun ℓ => view ℓ x ≠ view ℓ y)).Nonempty)
    (hD : δ * (n : ℝ) ≤
      ((Finset.univ.filter (fun ℓ => view ℓ x ≠ view ℓ y)).card : ℝ)) :
    ∃ q : β → β, ∃ Lstar : Finset (Fin n),
      (0 : ℝ) < (Lstar.card : ℝ) ∧
      δ * (n : ℝ) / (Fintype.card β : ℝ) ^ Fintype.card β ≤
        (Lstar.card : ℝ) ∧
      (∀ ℓ ∈ Lstar, ∀ h : β, view ℓ (q h) = view ℓ h) ∧
      (∀ ℓ ∈ Lstar, ∀ h h' : β,
        q h = q h' ↔ view ℓ h = view ℓ h') ∧
      2 ≤ (Finset.univ.image q).card := by
  classical
  letI : Nonempty β := hβ
  let part : Fin n → (β → β) := fun ℓ h =>
    Classical.choose (show ∃ z : β, view ℓ z = view ℓ h from ⟨h, rfl⟩)
  have hpart_view : ∀ ℓ (h : β), view ℓ (part ℓ h) = view ℓ h := by
    intro ℓ h
    exact Classical.choose_spec
      (show ∃ z : β, view ℓ z = view ℓ h from ⟨h, rfl⟩)
  have hpart_iff : ∀ ℓ (h h' : β),
      part ℓ h = part ℓ h' ↔ view ℓ h = view ℓ h' := by
    intro ℓ h h'
    constructor
    · intro heq
      calc
        view ℓ h = view ℓ (part ℓ h) := (hpart_view ℓ h).symm
        _ = view ℓ (part ℓ h') := congrArg (fun z : β => view ℓ z) heq
        _ = view ℓ h' := hpart_view ℓ h'
    · intro heq
      simp only [part, heq]
  let D : Finset (Fin n) :=
    Finset.univ.filter (fun ℓ => view ℓ x ≠ view ℓ y)
  let T : Finset (β → β) := Finset.univ
  have hTne : T.Nonempty := Finset.univ_nonempty
  obtain ⟨q, hqT, hqmax⟩ := Finset.exists_max_image T
    (fun q => (D.filter (fun ℓ => part ℓ = q)).card) hTne
  let Lstar : Finset (Fin n) := D.filter (fun ℓ => part ℓ = q)
  have hDtoT : ∀ ℓ ∈ D, part ℓ ∈ T := by
    intro ℓ hℓ
    exact Finset.mem_univ _
  have hcard_nat : D.card ≤ Lstar.card * T.card := by
    apply Finset.card_le_mul_card_image_of_maps_to hDtoT Lstar.card
    intro q' hq'
    change (D.filter (fun ℓ => part ℓ = q')).card ≤ Lstar.card
    exact hqmax q' hq'
  have hDne' : D.Nonempty := by
    simpa only [D] using hDne
  obtain ⟨ℓ0, hℓ0D⟩ := hDne'
  have hfiber_pos : 0 < (D.filter (fun ℓ => part ℓ = part ℓ0)).card := by
    apply Finset.card_pos.mpr
    exact ⟨ℓ0, Finset.mem_filter.mpr ⟨hℓ0D, rfl⟩⟩
  have hLpos : 0 < Lstar.card := by
    have hle := hqmax (part ℓ0) (Finset.mem_univ _)
    change (D.filter (fun ℓ => part ℓ = part ℓ0)).card ≤ Lstar.card at hle
    omega
  have hLc0 : (0 : ℝ) < (Lstar.card : ℝ) := by exact_mod_cast hLpos
  have hβpos : (0 : ℝ) < (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (Fintype.card β : ℝ) ^ Fintype.card β :=
    pow_pos hβpos (Fintype.card β)
  have hTcard : T.card = Fintype.card β ^ Fintype.card β := by
    simp only [T, Finset.card_univ, Fintype.card_fun]
  have hcard_real : (D.card : ℝ) ≤
      (Lstar.card : ℝ) * (Fintype.card β : ℝ) ^ Fintype.card β := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← hTcard]
    exact_mod_cast hcard_nat
  have hsize : δ * (n : ℝ) / (Fintype.card β : ℝ) ^ Fintype.card β ≤
      (Lstar.card : ℝ) := by
    apply (div_le_iff₀ hpow).2
    have hD' : δ * (n : ℝ) ≤ (D.card : ℝ) := by simpa only [D] using hD
    exact le_trans hD' hcard_real
  have hq_view : ∀ ℓ ∈ Lstar, ∀ h : β, view ℓ (q h) = view ℓ h := by
    intro ℓ hℓ h
    have hp : part ℓ = q := (Finset.mem_filter.mp hℓ).2
    rw [← hp]
    exact hpart_view ℓ h
  have hq_iff : ∀ ℓ ∈ Lstar, ∀ h h' : β,
      q h = q h' ↔ view ℓ h = view ℓ h' := by
    intro ℓ hℓ h h'
    have hp : part ℓ = q := (Finset.mem_filter.mp hℓ).2
    rw [← hp]
    exact hpart_iff ℓ h h'
  have hxy : q x ≠ q y := by
    intro heq
    obtain ⟨ℓ, hℓ⟩ := Finset.card_pos.mp hLpos
    have hℓD : ℓ ∈ D := (Finset.mem_filter.mp hℓ).1
    have hv := (hq_iff ℓ hℓ x y).mp heq
    exact (Finset.mem_filter.mp hℓD).2 hv
  have himage2 : 2 ≤ (Finset.univ.image q).card := by
    have hx : q x ∈ Finset.univ.image q := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    have hy : q y ∈ Finset.univ.image q := Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
    exact (Finset.one_lt_card.mpr ⟨q x, hx, q y, hy, hxy⟩)
  exact ⟨q, Lstar, hLc0, hsize, hq_view, hq_iff, himage2⟩

@[blueprint "lem:local-ael-partition-combine"
  (statement := /-- Let $H$ be a list of exactly $k$ AEL codewords, where $2\leq k\leq k_0$, and suppose a nontrivial partition map $q$ is constant as a local-view partition on a nonempty set $L^*$ with $\delta_{\mathrm{out}}n/k^k\leq |L^*|$. If every local view is an inner codeword and the AEL code is $(\delta_0,k-1,\varepsilon)$ average-radius list decodable with erasures, then the average-radius inequality with list bound $k$ holds for $H$. -/)
  (proof := /-- Index the parts by the image $R=q(H)$, so $p=|R|\geq2$, and let $H_r$ be the fibre over $r\in R$. Every fibre is nonempty and has at most $k-1$ elements. Apply \cref{lem:local-inductive-part-bound} to each fibre and sum; the fibre cardinalities sum to $k$, yielding the coefficient $k-p$. For each $\ell\in L^*$, the representative local views are distinct inner codewords, and \cref{lem:local-distance-bound} applies the inner average-radius hypothesis to give the coefficient $p-1$. The average local erasure fraction is at most the global erasure fraction plus $\varepsilon/6$ by \cref{lem:local-sampling-bound}. Hence the local contribution is at least $(p-1)(\delta_0-s-2\varepsilon/3)$. Combining both estimates leaves the target plus $(p-2)\varepsilon/6$, which is nonnegative. -/)
  (title := /-- Combining a constant local-view partition -/)
  (latexEnv := "lemma")]
lemma local_ael_partition_combine {n d k k0 : ℕ} {lam δ0 δout ε : ℝ}
    {α : Type*} [DecidableEq α]
    (hn : 0 < n) (hd : 0 < d) (hk : 2 ≤ k) (hkk0 : k ≤ k0) (hε : 0 < ε)
    (A : AELCode n d lam δout α)
    (hinner : AvgRadiusLDCErasures A.inner δ0 k0 (ε / 2))
    (hIH : AvgRadiusLDCErasures A.code δ0 (k - 1) ε)
    (hlamk : lam ≤ δout / (k : ℝ) ^ k * (ε / 6))
    (received : Fin n → Option (Fin d → α))
    (H : Finset (Fin n → (Fin d → α)))
    (hH : (↑H : Set (Fin n → (Fin d → α))) ⊆ A.code)
    (hHk : H.card = k)
    (view : Fin n → ↥H → (Fin d → α))
    (q : ↥H → ↥H) (Lstar : Finset (Fin n))
    (hLc0 : (0 : ℝ) < (Lstar.card : ℝ))
    (hLsize : δout * (n : ℝ) / (H.card : ℝ) ^ H.card ≤
      (Lstar.card : ℝ))
    (hq_view : ∀ ℓ ∈ Lstar, ∀ h : ↥H, view ℓ (q h) = view ℓ h)
    (hq_iff : ∀ ℓ ∈ Lstar, ∀ h h' : ↥H,
      q h = q h' ↔ view ℓ h = view ℓ h')
    (hqcard : 2 ≤ (Finset.univ.image q).card)
    (hview_inner : ∀ ℓ (h : ↥H), view ℓ h ∈ A.inner)
    (hview_def : ∀ ℓ (h : ↥H) i,
      view ℓ h i = h.val (A.edge (ℓ, i)).1 (A.edge (ℓ, i)).2) :
    ((H.card : ℝ) - 1) * (δ0 - erasureFrac received - ε) ≤
      ∑ h ∈ H, erasureDist received h := by
  classical
  have hLpos : 0 < Lstar.card := by exact_mod_cast hLc0
  obtain ⟨ℓ0, hℓ0⟩ := Finset.card_pos.mp hLpos
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  let h0 : ↥H := ⟨hHne.choose, hHne.choose_spec⟩
  let qH : (Fin n → (Fin d → α)) → ↥H := fun h =>
    if hh : h ∈ H then q ⟨h, hh⟩ else h0
  let R : Finset ↥H := H.image qH
  have hR_eq : R = Finset.univ.image q := by
    ext r
    simp only [R, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hh, hr⟩
      refine ⟨⟨h, hh⟩, ?_⟩
      simpa only [qH, dif_pos hh] using hr
    · rintro ⟨h, hr⟩
      refine ⟨h, h.property, ?_⟩
      simpa only [qH, dif_pos h.property] using hr
  have hRcard : 2 ≤ R.card := by rw [hR_eq]; exact hqcard
  have hq_fixed : ∀ r ∈ R, q r = r := by
    intro r hr
    rw [hR_eq, Finset.mem_image] at hr
    obtain ⟨h, -, rfl⟩ := hr
    exact (hq_iff ℓ0 hℓ0 (q h) h).mpr (hq_view ℓ0 hℓ0 h)
  have hview_inj : ∀ ℓ ∈ Lstar,
      Set.InjOn (view ℓ) (↑R : Set ↥H) := by
    intro ℓ hℓ u hu v hv huv
    have hquv : q u = q v := (hq_iff ℓ hℓ u v).mpr huv
    rw [hq_fixed u hu, hq_fixed v hv] at hquv
    exact hquv
  let Hj : ↥H → Finset (Fin n → (Fin d → α)) := fun r =>
    H.filter (fun h => qH h = r)
  have hHj_sub : ∀ r, (↑(Hj r) : Set (Fin n → (Fin d → α))) ⊆ A.code := by
    intro r h hh
    exact hH ((Finset.mem_filter.mp hh).1)
  have hHj_ne : ∀ r ∈ R, 1 ≤ (Hj r).card := by
    intro r hr
    change r ∈ H.image qH at hr
    rw [Finset.mem_image] at hr
    obtain ⟨h, hh, rfl⟩ := hr
    apply Finset.one_le_card.mpr
    exact ⟨h, Finset.mem_filter.mpr ⟨hh, rfl⟩⟩
  have hHj_card : ∀ r ∈ R, (Hj r).card ≤ k - 1 := by
    intro r hr
    have hr' : ∃ r' ∈ R, r' ≠ r := by
      by_contra hnone
      push Not at hnone
      have hsub : R ⊆ {r} := by
        intro z hz
        simpa [hnone z hz]
      have hcard1 : R.card ≤ 1 := by
        calc R.card ≤ ({r} : Finset ↥H).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton r
      omega
    obtain ⟨r', hr'R, hr'ne⟩ := hr'
    change r' ∈ H.image qH at hr'R
    rw [Finset.mem_image] at hr'R
    obtain ⟨h', hh', hq'⟩ := hr'R
    have hsub : Hj r ⊆ H := Finset.filter_subset _ _
    have hnot : h' ∉ Hj r := by
      simp only [Hj, Finset.mem_filter]
      intro hh
      exact hr'ne (hq'.symm.trans hh.2)
    have hproper : Hj r ⊂ H :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨hsub, fun heq => hnot (heq.symm ▸ hh')⟩
    have hlt : (Hj r).card < H.card := Finset.card_lt_card hproper
    omega
  let gloc : Fin n → (Fin d → Option α) := fun ℓ i =>
    Option.map (fun w : Fin d → α => w (A.edge (ℓ, i)).2)
      (received (A.edge (ℓ, i)).1)
  have hcommon : ∀ r, r ∈ R → ∀ h, ∀ hh : h ∈ Hj r, ∀ ℓ, ℓ ∈ Lstar →
      view ℓ r = view ℓ ⟨h, (Finset.mem_filter.mp hh).1⟩ := by
    intro r hr h hh ℓ hℓ
    have hhH : h ∈ H := (Finset.mem_filter.mp hh).1
    have hqr : qH h = r := (Finset.mem_filter.mp hh).2
    have hqsub : q ⟨h, hhH⟩ = r := by simpa only [qH, dif_pos hhH] using hqr
    have hv := hq_view ℓ hℓ ⟨h, hhH⟩
    rw [hqsub] at hv
    exact hv
  have hpart : ∀ r ∈ R,
      (((Hj r).card : ℝ) - 1) * (δ0 - erasureFrac received - ε) +
          (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (view ℓ r)) /
            (Lstar.card : ℝ) - ε / 6 ≤
        ∑ h ∈ Hj r, erasureDist received h := by
    intro r hr
    apply local_inductive_part_bound A.G A.code received (Hj r) Lstar gloc
      (fun ℓ => view ℓ r) A.edge hn hd (by omega) hε hLc0 hIH
      (hHj_sub r) (hHj_ne r hr) (hHj_card r hr) A.hEdgeMem A.hEdgeInj
    · intro ℓ i
      rfl
    · intro h hh ℓ hℓ i
      exact (congrFun (hcommon r hr h hh ℓ hℓ) i).trans
        (hview_def ℓ ⟨h, (Finset.mem_filter.mp hh).1⟩ i)
    · simpa only [hHk] using hLsize
    · exact hlamk
  have hq_maps : ∀ h ∈ H, qH h ∈ R := by
    intro h hh
    exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
  have hsum_fibers : ∑ r ∈ R, ∑ h ∈ Hj r, erasureDist received h =
      ∑ h ∈ H, erasureDist received h :=
    Finset.sum_fiberwise_of_maps_to hq_maps (fun h => erasureDist received h)
  have hcard_fibers : ∑ r ∈ R, (Hj r).card = H.card :=
    (Finset.card_eq_sum_card_fiberwise hq_maps).symm
  have hpart_sum := Finset.sum_le_sum (fun r hr => hpart r hr)
  rw [hsum_fibers] at hpart_sum
  have hpart_global :
      ((H.card : ℝ) - (R.card : ℝ)) * (δ0 - erasureFrac received - ε) +
        (∑ r ∈ R, (∑ ℓ ∈ Lstar,
          erasureDist (gloc ℓ) (view ℓ r)) / (Lstar.card : ℝ)) -
        (R.card : ℝ) * (ε / 6) ≤
      ∑ h ∈ H, erasureDist received h := by
    have hcard_real : ∑ r ∈ R, ((Hj r).card : ℝ) = (H.card : ℝ) := by
      exact_mod_cast hcard_fibers
    have hcoeff : ∑ r ∈ R, (((Hj r).card : ℝ) - 1) =
        (H.card : ℝ) - (R.card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      linarith
    calc
      _ = (∑ r ∈ R, (((Hj r).card : ℝ) - 1) *
              (δ0 - erasureFrac received - ε)) +
            (∑ r ∈ R, (∑ ℓ ∈ Lstar,
              erasureDist (gloc ℓ) (view ℓ r)) / (Lstar.card : ℝ)) -
            (R.card : ℝ) * (ε / 6) := by
              rw [← hcoeff, Finset.sum_mul]
      _ = ∑ r ∈ R,
          ((((Hj r).card : ℝ) - 1) * (δ0 - erasureFrac received - ε) +
            (∑ ℓ ∈ Lstar, erasureDist (gloc ℓ) (view ℓ r)) /
              (Lstar.card : ℝ) - ε / 6) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := hpart_sum
  have hRle : R.card ≤ k0 := by
    have himage : R.card ≤ H.card := Finset.card_image_le
    omega
  have hlocal : ∀ ℓ ∈ Lstar,
      ((R.card : ℝ) - 1) * (δ0 - erasureFrac (gloc ℓ) - ε / 2) ≤
        ∑ r ∈ R, erasureDist (gloc ℓ) (view ℓ r) := by
    intro ℓ hℓ
    let F : Finset (Fin d → α) := R.image (view ℓ)
    have hFinj : Set.InjOn (view ℓ) (↑R : Set ↥H) := hview_inj ℓ hℓ
    have hFcard : F.card = R.card := Finset.card_image_iff.mpr hFinj
    have hFmem : (↑F : Set (Fin d → α)) ⊆ A.inner := by
      intro f hf
      change f ∈ R.image (view ℓ) at hf
      rw [Finset.mem_image] at hf
      obtain ⟨r, hr, rfl⟩ := hf
      exact hview_inner ℓ r
    have hi := local_distance_bound A.inner hinner (gloc ℓ) F hFmem
      (by rw [hFcard]; omega) (by rw [hFcard]; exact hRle)
    rw [hFcard] at hi
    have hsum : ∑ f ∈ F, erasureDist (gloc ℓ) f =
        ∑ r ∈ R, erasureDist (gloc ℓ) (view ℓ r) := by
      change (∑ f ∈ R.image (view ℓ), erasureDist (gloc ℓ) f) = _
      rw [Finset.sum_image]
      intro u hu v hv huv
      exact hFinj hu hv huv
    rw [hsum] at hi
    exact hi
  let S : Finset (Fin n) := Finset.univ.filter (fun r => received r = none)
  have herase_pt : ∀ ℓ ∈ Lstar,
      erasureFrac (gloc ℓ) ≤ ((A.G.nbrs ℓ ∩ S).card : ℝ) / (d : ℝ) := by
    intro ℓ hℓ
    have himg : (Finset.univ.filter (fun i : Fin d => gloc ℓ i = none)).image
        (fun i : Fin d => (A.edge (ℓ, i)).1) ⊆ A.G.nbrs ℓ ∩ S := by
      intro r hr
      rw [Finset.mem_image] at hr
      obtain ⟨i, hi, rfl⟩ := hr
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_inter]
      refine ⟨A.hEdgeMem ℓ i, ?_⟩
      simp only [S, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [gloc, Option.map_eq_none_iff] using hi.2
    have hcard : (Finset.univ.filter (fun i : Fin d => gloc ℓ i = none)).card ≤
        (A.G.nbrs ℓ ∩ S).card := by
      calc
        _ = ((Finset.univ.filter (fun i : Fin d => gloc ℓ i = none)).image
              (fun i : Fin d => (A.edge (ℓ, i)).1)).card :=
          (Finset.card_image_of_injective _ (A.hEdgeInj ℓ)).symm
        _ ≤ _ := Finset.card_le_card himg
    simp only [erasureFrac]
    gcongr
  have herase_sum : (∑ ℓ ∈ Lstar, erasureFrac (gloc ℓ)) /
      (Lstar.card : ℝ) ≤ erasureFrac received + ε / 6 := by
    have hsum := Finset.sum_le_sum herase_pt
    have hsamp := local_sampling_bound A.G Lstar S hn hd (by omega) hε
      hLc0 (by simpa only [hHk] using hLsize) hlamk
    have hdiv : (∑ ℓ ∈ Lstar, erasureFrac (gloc ℓ)) /
        (Lstar.card : ℝ) ≤
        (∑ ℓ ∈ Lstar, ((A.G.nbrs ℓ ∩ S).card : ℝ) / (d : ℝ)) /
          (Lstar.card : ℝ) := by
      gcongr
    have hSfrac : (S.card : ℝ) / (n : ℝ) = erasureFrac received := by rfl
    rw [hSfrac] at hsamp
    exact le_trans hdiv hsamp
  have hlocal_global :
      ((R.card : ℝ) - 1) *
          (δ0 - erasureFrac received - 2 * ε / 3) ≤
        ∑ r ∈ R, (∑ ℓ ∈ Lstar,
          erasureDist (gloc ℓ) (view ℓ r)) / (Lstar.card : ℝ) := by
    have hRone : (1 : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast (by omega : 1 ≤ R.card)
    have hRnonneg : 0 ≤ (R.card : ℝ) - 1 := by linarith
    have hlocal_avg :
        ((R.card : ℝ) - 1) *
            (δ0 - (∑ ℓ ∈ Lstar, erasureFrac (gloc ℓ)) /
              (Lstar.card : ℝ) - ε / 2) ≤
          ∑ r ∈ R, (∑ ℓ ∈ Lstar,
            erasureDist (gloc ℓ) (view ℓ r)) / (Lstar.card : ℝ) := by
      have hLcne : (Lstar.card : ℝ) ≠ 0 := ne_of_gt hLc0
      have hsum_expand :
          (∑ ℓ ∈ Lstar, ((R.card : ℝ) - 1) *
            (δ0 - erasureFrac (gloc ℓ) - ε / 2)) =
          (Lstar.card : ℝ) * (((R.card : ℝ) - 1) * (δ0 - ε / 2)) -
            ((R.card : ℝ) - 1) *
              (∑ ℓ ∈ Lstar, erasureFrac (gloc ℓ)) := by
        calc
          _ = ∑ ℓ ∈ Lstar,
              (((R.card : ℝ) - 1) * (δ0 - ε / 2) -
                ((R.card : ℝ) - 1) * erasureFrac (gloc ℓ)) := by
                  apply Finset.sum_congr rfl
                  intro ℓ hℓ
                  ring
          _ = (∑ ℓ ∈ Lstar, ((R.card : ℝ) - 1) * (δ0 - ε / 2)) -
              (∑ ℓ ∈ Lstar, ((R.card : ℝ) - 1) * erasureFrac (gloc ℓ)) :=
                by rw [Finset.sum_sub_distrib]
          _ = _ := by
                rw [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
      have havg_eq :
          ((R.card : ℝ) - 1) *
              (δ0 - (∑ ℓ ∈ Lstar, erasureFrac (gloc ℓ)) /
                (Lstar.card : ℝ) - ε / 2) =
            (∑ ℓ ∈ Lstar, ((R.card : ℝ) - 1) *
              (δ0 - erasureFrac (gloc ℓ) - ε / 2)) /
                (Lstar.card : ℝ) := by
        rw [hsum_expand]
        field_simp [hLcne]
        ring
      rw [havg_eq]
      calc
        _ ≤ (∑ ℓ ∈ Lstar, ∑ r ∈ R,
              erasureDist (gloc ℓ) (view ℓ r)) /
              (Lstar.card : ℝ) := by
                apply (div_le_div_iff_of_pos_right hLc0).2
                exact Finset.sum_le_sum hlocal
        _ = _ := by
              rw [Finset.sum_comm, ← Finset.sum_div]
    have hbase : δ0 - erasureFrac received - 2 * ε / 3 ≤
        δ0 - (∑ ℓ ∈ Lstar, erasureFrac (gloc ℓ)) /
          (Lstar.card : ℝ) - ε / 2 := by
      linarith [herase_sum]
    exact le_trans (mul_le_mul_of_nonneg_left hbase hRnonneg) hlocal_avg
  have hRtwo : (2 : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast hRcard
  nlinarith [hpart_global, hlocal_global, hε, hRtwo]

@[blueprint "lem:local-ael-inductive-step"
  (statement := /-- Let $2\leq k\leq k_0$, let $n,d\geq 1$, and let $A$ be an AEL code whose inner code is $(\delta_0,k_0,\varepsilon/2)$ average-radius list decodable with erasures. Assume that $A$ is $(\delta_0,k-1,\varepsilon)$ average-radius list decodable with erasures and that $\lambda\leq \delta_{\mathrm{out}}\varepsilon/(6k^k)$. Then $A$ is $(\delta_0,k,\varepsilon)$ average-radius list decodable with erasures. -/)
  (proof := /-- Fix a received word and a nonempty list $H\subseteq A$ of at most $k$ codewords. If $|H|\leq k-1$, the asserted inequality is the induction hypothesis. Otherwise $|H|=k\geq2$; choose distinct $h_1,h_2\in H$. The AEL encoding map is injective because the inner encoding and the edge permutation are injective, so each $h\in H$ has a uniquely determined outer preimage $c_h$, and $c_{h_1}\neq c_{h_2}$. At a left vertex $\ell$, define the local view of $h$ by reading $h$ along the ports incident to $\ell$; this view equals the inner encoding of $c_h(\ell)$. Consequently the local views of $h_1$ and $h_2$ differ precisely where $c_{h_1}$ and $c_{h_2}$ differ. The outer-distance hypothesis therefore gives a nonempty set of such vertices of cardinality at least $\delta_{\mathrm{out}}n$. Applying \cref{lem:local-partition-pigeonhole} yields a representative map $q$ and a nonempty set $L^*$ with $|L^*|\geq \delta_{\mathrm{out}}n/k^k$ on which equality of representatives is equivalent to equality of local views; the image of $q$ has at least two elements. Every local view lies in the inner code. Thus all hypotheses of \cref{lem:local-ael-partition-combine} hold, and that lemma supplies the required average-radius inequality for $H$. -/)
  (title := /-- Inductive AEL amplification step -/)
  (latexEnv := "lemma")]
lemma local_ael_inductive_step {n d k k0 : ℕ} {lam δ0 δout ε : ℝ}
    {α : Type*} [DecidableEq α]
    (hn : 0 < n) (hd : 0 < d) (hk : 2 ≤ k) (hkk0 : k ≤ k0) (hε : 0 < ε)
    (A : AELCode n d lam δout α)
    (hinner : AvgRadiusLDCErasures A.inner δ0 k0 (ε / 2))
    (hIH : AvgRadiusLDCErasures A.code δ0 (k - 1) ε)
    (hlamk : lam ≤ δout / (k : ℝ) ^ k * (ε / 6)) :
    AvgRadiusLDCErasures A.code δ0 k ε := by
  classical
  intro received H hH hHne hHcard
  by_cases hsmall : H.card ≤ k - 1
  · exact hIH received H hH hHne hsmall
  have hHk : H.card = k := by omega
  have hHtwo : 1 < H.card := by omega
  obtain ⟨h1, hh1, h2, hh2, hh12⟩ := Finset.one_lt_card.mp hHtwo
  let x : ↥H := ⟨h1, hh1⟩
  let y : ↥H := ⟨h2, hh2⟩
  let enc : (Fin n → α) → (Fin n → (Fin d → α)) := fun c r j =>
    A.innerEnc (c (A.edge.symm (r, j)).1) (A.edge.symm (r, j)).2
  have hex : ∀ h : ↥H, ∃ c ∈ A.outer, enc c = (h : Fin n → (Fin d → α)) := by
    intro h
    have hm : (h : Fin n → (Fin d → α)) ∈ A.code := hH h.property
    rw [A.hCode] at hm
    exact hm
  let outerOf : ↥H → (Fin n → α) := fun h => Classical.choose (hex h)
  have houter_mem : ∀ h : ↥H, outerOf h ∈ A.outer := by
    intro h
    exact (Classical.choose_spec (hex h)).1
  have houter_eq : ∀ h : ↥H,
      enc (outerOf h) = (h : Fin n → (Fin d → α)) := by
    intro h
    exact (Classical.choose_spec (hex h)).2
  have houter_inj : Function.Injective outerOf := by
    intro u v huv
    apply Subtype.ext
    rw [← houter_eq u, ← houter_eq v, huv]
  let view : Fin n → ↥H → (Fin d → α) := fun ℓ h i =>
    h.val (A.edge (ℓ, i)).1 (A.edge (ℓ, i)).2
  have hview : ∀ ℓ (h : ↥H), view ℓ h = A.innerEnc (outerOf h ℓ) := by
    intro ℓ h
    funext i
    have heq := congrFun (congrFun (houter_eq h) (A.edge (ℓ, i)).1)
      (A.edge (ℓ, i)).2
    change A.innerEnc
      (outerOf h (A.edge.symm ((A.edge (ℓ, i)).1, (A.edge (ℓ, i)).2)).1)
      (A.edge.symm ((A.edge (ℓ, i)).1, (A.edge (ℓ, i)).2)).2 =
        h.val (A.edge (ℓ, i)).1 (A.edge (ℓ, i)).2 at heq
    have hp : ((A.edge (ℓ, i)).1, (A.edge (ℓ, i)).2) = A.edge (ℓ, i) :=
      Prod.eta _
    rw [hp, Equiv.symm_apply_apply] at heq
    exact heq.symm
  have hxy_outer : outerOf x ≠ outerOf y := by
    intro heq
    have hsub : x = y := houter_inj heq
    exact hh12 (congrArg Subtype.val hsub)
  have hview_iff : ∀ ℓ (u v : ↥H),
      view ℓ u = view ℓ v ↔ outerOf u ℓ = outerOf v ℓ := by
    intro ℓ u v
    constructor
    · intro huv
      apply A.hEncInj
      calc
        A.innerEnc (outerOf u ℓ) = view ℓ u := (hview ℓ u).symm
        _ = view ℓ v := huv
        _ = A.innerEnc (outerOf v ℓ) := hview ℓ v
    · intro huv
      calc
        view ℓ u = A.innerEnc (outerOf u ℓ) := hview ℓ u
        _ = A.innerEnc (outerOf v ℓ) := congrArg A.innerEnc huv
        _ = view ℓ v := (hview ℓ v).symm
  have hD_eq : Finset.univ.filter (fun ℓ => view ℓ x ≠ view ℓ y) =
      Finset.univ.filter (fun ℓ => outerOf x ℓ ≠ outerOf y ℓ) := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_congr (hview_iff ℓ x y)
  have hDne : (Finset.univ.filter (fun ℓ => view ℓ x ≠ view ℓ y)).Nonempty := by
    have hexcoord : ∃ ℓ, outerOf x ℓ ≠ outerOf y ℓ := by
      by_contra hnone
      push Not at hnone
      exact hxy_outer (funext hnone)
    obtain ⟨ℓ, hℓ⟩ := hexcoord
    rw [hD_eq]
    exact ⟨ℓ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ⟩⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hD : δout * (n : ℝ) ≤
      ((Finset.univ.filter (fun ℓ => view ℓ x ≠ view ℓ y)).card : ℝ) := by
    have hout := A.hOuterDist (outerOf x) (houter_mem x)
      (outerOf y) (houter_mem y) hxy_outer
    have hmul := (le_div_iff₀ hn0).mp hout
    rw [hD_eq]
    exact hmul
  obtain ⟨q, Lstar, hLc0, hLsize, hq_view, hq_iff, hqcard⟩ :=
    local_partition_pigeonhole (n := n) (δ := δout)
      (β := ↥H) (γ := Fin d → α) view x y ⟨x⟩ hDne hD
  have hLsize' : δout * (n : ℝ) / (H.card : ℝ) ^ H.card ≤
      (Lstar.card : ℝ) := by
    simpa only [Fintype.card_coe] using hLsize
  apply local_ael_partition_combine hn hd hk hkk0 hε A hinner hIH hlamk
    received H hH hHk view q Lstar hLc0 hLsize' hq_view hq_iff hqcard
  · intro ℓ h
    rw [hview ℓ h]
    exact A.hEncMem (outerOf h ℓ)
  · intro ℓ h i
    rfl

@[blueprint "thm:main-technical-avg"
  (statement := /-- Let $k_0 \ge 1$ be an integer and let $\varepsilon > 0$. Let $C_{\mathrm{AEL}}$ be the code obtained by the AEL construction from $(G, C_{\mathrm{out}}, C_{\mathrm{in}})$, where the inner code $C_{\mathrm{in}}$ is $(\delta_0, k_0, \varepsilon/2)$ average-radius list decodable with erasures and $G$ is an $(n, d, \lambda)$-expander with $\lambda \le \frac{\delta_{\mathrm{out}}}{6\, k_0^{\,k_0}} \cdot \varepsilon$, and $\delta_{\mathrm{out}}$ is the relative distance of the outer code $C_{\mathrm{out}}$. Then $C_{\mathrm{AEL}}$ is $(\delta_0, k_0, \varepsilon)$ average-radius list decodable with erasures. -/)
  (proof := /-- If $n=0$ or $d=0$, any finite set of words of the relevant type has at most one element, so the defining inequality follows from \cref{lem:base-case-avg-ldc}. Assume henceforth that $n,d\geq1$. Applying the expander mixing inequality to the empty sets gives $\lambda\geq0$. Rewriting the spectral hypothesis as $\lambda\leq (\delta_{\mathrm{out}}/k_0^{k_0})(\varepsilon/6)$, and using $\varepsilon>0$, yields $\delta_{\mathrm{out}}\geq0$. We prove by induction on $m$, for $1\leq m\leq k_0$, that the AEL code is $(\delta_0,m,\varepsilon)$ average-radius list decodable with erasures. The case $m=1$ is \cref{lem:base-case-avg-ldc}. For the step from $m$ to $m+1$, where $m+1\leq k_0$, monotonicity of $t\mapsto t^t$ on positive integers gives $(m+1)^{m+1}\leq k_0^{k_0}$. Since $\delta_{\mathrm{out}}\geq0$, this weakens the spectral bound to $\lambda\leq (\delta_{\mathrm{out}}/(m+1)^{m+1})(\varepsilon/6)$. The induction hypothesis and \cref{lem:local-ael-inductive-step} then prove the assertion for $m+1$. Taking $m=k_0$ gives the theorem. -/)
  (title := /-- Local-to-global amplification of average-radius list decodability with erasures via AEL -/)
  (latexEnv := "theorem")]
theorem main_technical_avg {n d k0 : ℕ} {lam δ0 δout ε : ℝ} {α : Type*} [DecidableEq α]
    (hk : 1 ≤ k0) (hε : 0 < ε)
    (A : AELCode n d lam δout α)
    (hinner : AvgRadiusLDCErasures A.inner δ0 k0 (ε / 2))
    (hlam : lam ≤ δout / (6 * (k0 : ℝ) ^ k0) * ε) :
    AvgRadiusLDCErasures A.code δ0 k0 ε := by
  classical
  by_cases hnzero : n = 0
  · intro received H hH hHne hHcard
    apply base_case_avg_ldc δ0 ε received H hHne
    apply Finset.card_le_one.mpr
    intro u hu v hv
    funext r
    exact Fin.elim0 (hnzero ▸ r)
  by_cases hdzero : d = 0
  · intro received H hH hHne hHcard
    apply base_case_avg_ldc δ0 ε received H hHne
    apply Finset.card_le_one.mpr
    intro u hu v hv
    funext r i
    exact Fin.elim0 (hdzero ▸ i)
  have hn : 0 < n := Nat.pos_of_ne_zero hnzero
  have hd : 0 < d := Nat.pos_of_ne_zero hdzero
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hk00 : (0 : ℝ) < (k0 : ℝ) := by exact_mod_cast hk
  have hKpos : (0 : ℝ) < (k0 : ℝ) ^ k0 := pow_pos hk00 k0
  have hlam0 : (0 : ℝ) ≤ lam := by
    have hmix := A.G.mixing ∅ ∅
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
      zero_mul, sub_zero, abs_zero] at hmix
    nlinarith [hmix, mul_pos hd0 hn0]
  have hlam_norm : lam ≤ δout / (k0 : ℝ) ^ k0 * (ε / 6) := by
    calc
      lam ≤ δout / (6 * (k0 : ℝ) ^ k0) * ε := hlam
      _ = δout / (k0 : ℝ) ^ k0 * (ε / 6) := by ring
  have hε6 : (0 : ℝ) < ε / 6 := by linarith
  have hδdiv : (0 : ℝ) ≤ δout / (k0 : ℝ) ^ k0 := by
    by_contra hneg
    have hmulneg : δout / (k0 : ℝ) ^ k0 * (ε / 6) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hε6
    linarith [hlam0, hlam_norm]
  have hδout : (0 : ℝ) ≤ δout := by
    have hmul := mul_nonneg hδdiv (le_of_lt hKpos)
    have heq : δout / (k0 : ℝ) ^ k0 * (k0 : ℝ) ^ k0 = δout :=
      div_mul_cancel₀ δout (ne_of_gt hKpos)
    linarith
  have hall : ∀ m : ℕ, 1 ≤ m → m ≤ k0 →
      AvgRadiusLDCErasures A.code δ0 m ε := by
    intro m
    induction m with
    | zero =>
        intro hm
        omega
    | succ m ih =>
        intro hm1 hmk0
        by_cases hmzero : m = 0
        · subst m
          intro received H hH hHne hHcard
          exact base_case_avg_ldc δ0 ε received H hHne hHcard
        · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hmzero
          have hIH : AvgRadiusLDCErasures A.code δ0 m ε :=
            ih hmpos (by omega)
          have hmstep : 2 ≤ m + 1 := by omega
          have hpownat : (m + 1) ^ (m + 1) ≤ k0 ^ k0 := by
            calc
              (m + 1) ^ (m + 1) ≤ k0 ^ (m + 1) :=
                Nat.pow_le_pow_left hmk0 (m + 1)
              _ ≤ k0 ^ k0 := Nat.pow_le_pow_right (by omega) hmk0
          have hpowreal : ((m + 1 : ℕ) : ℝ) ^ (m + 1) ≤
              (k0 : ℝ) ^ k0 := by exact_mod_cast hpownat
          have hmreal : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by
            positivity
          have hfrac : δout / (k0 : ℝ) ^ k0 ≤
              δout / (((m + 1 : ℕ) : ℝ) ^ (m + 1)) :=
            div_le_div_of_nonneg_left hδout hmreal hpowreal
          have hlamstep : lam ≤
              δout / (((m + 1 : ℕ) : ℝ) ^ (m + 1)) * (ε / 6) :=
            le_trans hlam_norm
              (mul_le_mul_of_nonneg_right hfrac (le_of_lt hε6))
          simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using
            local_ael_inductive_step hn hd hmstep hmk0 hε A hinner hIH hlamstep
  exact hall k0 hk le_rfl

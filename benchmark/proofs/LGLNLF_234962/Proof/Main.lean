import Architect
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Operations

set_option linter.all false
set_option maxHeartbeats 500000

@[blueprint "def:generation-language"
  (statement := /-- A generation language is an infinite subset of the universe
  \(\mathbb{Z}\). -/)
  (title := /-- Generation language -/)
  (latexEnv := "definition")]
structure generation_language where
  carrier : Set Int
  infinite_carrier : carrier.Infinite

@[blueprint "def:language-collection"
  (statement := /-- A language collection is an arbitrary, possibly uncountable,
  set of generation languages. -/)
  (title := /-- Collection of languages -/)
  (latexEnv := "definition")]
abbrev language_collection := Set generation_language

@[blueprint "def:sample-free-generator"
  (statement := /-- A generator without samples is represented by its output
  sequence \(z\colon\mathbb{N}\to\mathbb{Z}\).  Thus \(z_t\) is fixed without
  access to any adversarial enumeration. -/)
  (title := /-- Generator without samples -/)
  (latexEnv := "definition")]
abbrev sample_free_generator := Nat → Int

@[blueprint "def:generated-before"
  (statement := /-- For a sample-free output sequence \(z\) and time
  \(t\in\mathbb{N}\), the set generated before time \(t\) is
  \(\{u\in\mathbb{Z}:\exists i<t,\ z_i=u\}\). -/)
  (title := /-- Outputs generated before a time -/)
  (latexEnv := "definition")]
def generated_before (z : sample_free_generator) (t : Nat) : Set Int :=
  {u | ∃ i < t, z i = u}

@[blueprint "def:sample-free-fresh-for"
  (statement := /-- The output of a sample-free generator \(z\) at time \(t\)
  is fresh for a language \(K\) if \(z_t\in K\) and \(z_t\) has not occurred at
  any earlier time. -/)
  (title := /-- Fresh sample-free output -/)
  (latexEnv := "definition")]
def sample_free_fresh_for
    (z : sample_free_generator) (K : generation_language) (t : Nat) : Prop :=
  z t ∈ K.carrier ∧ z t ∉ generated_before z t

@[blueprint "def:nonuniformly-generatable-without-samples"
  (statement := /-- A collection \(\mathcal C\) is non-uniformly generatable
  without samples if there is one sample-free generator \(z\) such that, for
  every \(K\in\mathcal C\), there is a time \(t_K\) after which every output is
  fresh for \(K\).  The threshold may depend on \(K\). -/)
  (title := /-- Non-uniform generation without samples -/)
  (latexEnv := "definition")]
def nonuniformly_generatable_without_samples (C : language_collection) : Prop :=
  ∃ z : sample_free_generator, ∀ K ∈ C, ∃ t₀ : Nat, ∀ t ≥ t₀,
    sample_free_fresh_for z K t

@[blueprint "def:uniformly-generatable-without-samples"
  (statement := /-- A collection \(\mathcal C\) is uniformly generatable
  without samples if there are a sample-free generator \(z\) and a single time
  \(t_0\) such that, for every \(K\in\mathcal C\) and every \(t\geq t_0\), the
  output \(z_t\) is fresh for \(K\). -/)
  (title := /-- Uniform generation without samples -/)
  (latexEnv := "definition")]
def uniformly_generatable_without_samples (C : language_collection) : Prop :=
  ∃ z : sample_free_generator, ∃ t₀ : Nat, ∀ K ∈ C, ∀ t ≥ t₀,
    sample_free_fresh_for z K t

@[blueprint "def:sample-based-generator"
  (statement := /-- A sample-based generator is a function from a finite
  ordered list of observed strings to one output string in \(\mathbb{Z}\). -/)
  (title := /-- Sample-based generator -/)
  (latexEnv := "definition")]
abbrev sample_based_generator := List Int → Int

@[blueprint "def:enumerates-language"
  (statement := /-- A sequence \(x\colon\mathbb{N}\to\mathbb{Z}\) enumerates a
  language \(K\) if its range is exactly the carrier of \(K\). -/)
  (title := /-- Enumeration of a language -/)
  (latexEnv := "definition")]
def enumerates_language (x : Nat → Int) (K : generation_language) : Prop :=
  Set.range x = K.carrier

@[blueprint "def:enumeration-prefix"
  (statement := /-- For an enumeration \(x\) and time \(t\), its ordered prefix
  is the list \([x_0,x_1,\ldots,x_t]\). -/)
  (title := /-- Finite ordered enumeration prefix -/)
  (latexEnv := "definition")]
def enumeration_prefix (x : Nat → Int) (t : Nat) : List Int :=
  List.ofFn (fun i : Fin (t + 1) => x i.val)

@[blueprint "def:seen-prefix"
  (statement := /-- For an enumeration \(x\) and time \(t\), the seen set is
  \(S_t(x)=\{u\in\mathbb{Z}:\exists i\leq t,\ x_i=u\}\). -/)
  (title := /-- Strings seen by a time -/)
  (latexEnv := "definition")]
def seen_prefix (x : Nat → Int) (t : Nat) : Set Int :=
  {u | ∃ i ≤ t, x i = u}

@[blueprint "def:sample-based-fresh-for"
  (statement := /-- A sample-based generator \(G\), receiving the ordered
  prefix \([x_0,\ldots,x_t]\), is fresh for \(K\) at time \(t\) if its output
  belongs to \(K\) and does not belong to the seen set \(S_t(x)\). -/)
  (title := /-- Fresh output relative to observed samples -/)
  (latexEnv := "definition")]
def sample_based_fresh_for
    (G : sample_based_generator) (x : Nat → Int)
    (K : generation_language) (t : Nat) : Prop :=
  G (enumeration_prefix x t) ∈ K.carrier ∧
    G (enumeration_prefix x t) ∉ seen_prefix x t

@[blueprint "def:generates-in-limit"
  (statement := /-- A generator \(G\) generates in the limit for a collection
  \(\mathcal C\) if, for every \(K\in\mathcal C\) and every enumeration \(x\)
  of \(K\), there is a threshold \(t_{K,x}\) such that every output from that
  time onward lies in \(K\setminus S_t(x)\). -/)
  (title := /-- Generation in the limit by a fixed generator -/)
  (latexEnv := "definition")]
def generates_in_limit (G : sample_based_generator) (C : language_collection) : Prop :=
  ∀ K ∈ C, ∀ x : Nat → Int, enumerates_language x K →
    ∃ t₀ : Nat, ∀ t ≥ t₀, sample_based_fresh_for G x K t

@[blueprint "def:generatable-in-limit"
  (statement := /-- A collection \(\mathcal C\) is generatable in the limit if
  some sample-based generator generates in the limit for \(\mathcal C\) in the
  sense of \cref{def:generates-in-limit}. -/)
  (title := /-- Collection generatable in the limit -/)
  (latexEnv := "definition")]
def generatable_in_limit (C : language_collection) : Prop :=
  ∃ G : sample_based_generator, generates_in_limit G C

@[blueprint "def:separating-collections"
  (statement := /-- Two collections \(\mathcal C_1,\mathcal C_2\) separate the
  generation notions if \(\mathcal C_1\) is non-uniformly generatable without
  samples, \(\mathcal C_2\) is uniformly generatable without samples, and
  \(\mathcal C_1\cup\mathcal C_2\) is not generatable in the limit. -/)
  (title := /-- Separation package for two collections -/)
  (latexEnv := "definition")]
def separating_collections (C₁ C₂ : language_collection) : Prop :=
  nonuniformly_generatable_without_samples C₁ ∧
    uniformly_generatable_without_samples C₂ ∧
    ¬ generatable_in_limit (C₁ ∪ C₂)

@[blueprint "lem:separating-collections-exist"
  (statement := /-- There exist language collections
  \(\mathcal C_1,\mathcal C_2\) satisfying the separation package of
  \cref{def:separating-collections}. -/)
  (proof := /-- Write (p_n=n) and (m_n=-n-1) for the nonnegative and
  negative integers, respectively.  Let (mathcal C_1) consist of the
  generation languages whose carriers contain ({p_{N+j}:j\in\mathbb N})
  for some (N), and let (mathcal C_2) consist of those whose carriers
  contain every (m_n).  The injective sequence ((p_n)) generates every
  member of (mathcal C_1) after its associated cutoff, whereas the injective
  sequence ((m_n)) generates every member of (mathcal C_2) from time zero.
  Thus the two collections satisfy the positive clauses of
  cref{def:separating-collections} by
  cref{def:nonuniformly-generatable-without-samples,
  def:uniformly-generatable-without-samples}; freshness is exactly the
  conjunction in cref{def:sample-free-fresh-for}, since each sequence has no
  repeated earlier output as recorded by cref{def:generated-before}.

  Suppose, contrary to the remaining clause, that a sample-based generator
  (G) generates (mathcal C_1\cup\mathcal C_2) in the sense of
  cref{def:generatable-in-limit,def:generates-in-limit}.  Construct nested
  finite injective lists (s_n) and strictly increasing cutoffs (N_n).
  Given (s_n,N_n), enumerate first (s_n) and then the positive tail
  ((p_{N_n+j})_{j\geq0}).  This enumeration is a member of
  (mathcal C_1), so after some time (q_n\geq |s_n|), the output of (G)
  is fresh.  It cannot be an element of (s_n), all of which have already
  appeared; hence it is (p_{k_n}) for some (k_n\geq N_n).  Let
  (s_{n+1}) be the enumeration prefix through time (q_n), followed by
  (m_n), and choose (N_{n+1}) larger than (k_n) and than every positive
  index occurring in that prefix.  Consequently (p_{k_n}) occurs neither
  in (s_{n+1}) nor in its positive tail, and induction shows that it never
  occurs in any later list or tail.  The prefix used here is precisely
  cref{def:enumeration-prefix}, and freshness excludes its seen elements by
  cref{def:sample-based-fresh-for,def:seen-prefix}.

  The nested lists determine an injective limiting sequence (x).  Its range
  is infinite and contains every (m_n), so it is the carrier of a language
  (K\in\mathcal C_2), and (x) enumerates (K) according to
  cref{def:enumerates-language}.  For every (n), at the time (q_n) the
  prefix of (x) agrees with the stage-(n) prefix, so (G) outputs
  (p_{k_n}\notin K).  Since (q_n\geq n), these failures occur arbitrarily
  late, contradicting generation in the limit.  Therefore
  (mathcal C_1\cup\mathcal C_2) is not generatable in the limit, and the
  two constructed collections satisfy cref{def:separating-collections}. -/)
  (title := /-- Existence of separating collections -/)
  (latexEnv := "lemma")]
lemma separating_collections_exist :
    ∃ C₁ C₂ : language_collection, separating_collections C₁ C₂ := by
  classical
  let pos : Nat → Int := fun n => Int.ofNat n
  let neg : Nat → Int := fun n => Int.negSucc n
  let tail (N : Nat) : Set Int := Set.range (fun k => pos (N + k))
  have nat_not_finite : ¬ Finite Nat := by
    intro hfin
    cases hfin with
    | @intro n q =>
        let l : List Nat := List.ofFn (fun i : Fin n => q.symm i)
        let M := l.foldr max 0
        have le_fold : ∀ (r : List Nat) (a : Nat), a ∈ r → a ≤ r.foldr max 0 := by
          intro r
          induction r with
          | nil => intro a ha; contradiction
          | cons b r ih =>
              intro a ha
              cases ha with
              | head => exact Nat.le_max_left _ _
              | tail _ ha =>
                  exact Nat.le_trans (ih a ha) (Nat.le_max_right _ _)
        have hmem : q.symm (q (M + 1)) ∈ l := by
          let i := q (M + 1)
          have hi : i.val < l.length := by simp [l, i]
          have heq : l[i.val] = q.symm i := by simp [l, i]
          rw [← heq]
          exact List.getElem_mem ..
        have hle := le_fold l _ hmem
        dsimp [M] at hle
        have : M + 1 ≤ M := by simpa using hle
        omega
  have range_infinite {f : Nat → Int} (hf : Function.Injective f) :
      (Set.range f).Infinite := by
    intro hfin
    let e : Nat ≃ {u // u ∈ Set.range f} :=
      { toFun := fun n => ⟨f n, ⟨n, rfl⟩⟩
        invFun := fun u => Classical.choose u.property
        left_inv := fun n => hf (Classical.choose_spec
          (show f n ∈ Set.range f from ⟨n, rfl⟩))
        right_inv := fun u => Subtype.ext (Classical.choose_spec u.property) }
    cases hfin with
    | intro q => exact nat_not_finite (Finite.intro (e.trans q))
  let enum (s : List Int) (N : Nat) : Nat → Int := fun k =>
    if h : k < s.length then s[k] else pos (N + (k - s.length))
  have enum_injective (s : List Int) (N : Nat)
      (hs : ∀ a b (ha : a < s.length) (hb : b < s.length), s[a] = s[b] → a = b)
      (hdis : ∀ u ∈ s, u ∉ tail N) : Function.Injective (enum s N) := by
    intro a b hab
    by_cases ha : a < s.length <;> by_cases hb : b < s.length
    · exact hs a b ha hb (by simpa [enum, ha, hb] using hab)
    · exfalso
      apply hdis s[a] (List.getElem_mem ..)
      exact ⟨b - s.length, by simpa [enum, tail, ha, hb] using hab.symm⟩
    · exfalso
      apply hdis s[b] (List.getElem_mem ..)
      exact ⟨a - s.length, by simpa [enum, tail, ha, hb] using hab⟩
    · simp [enum, pos, ha, hb] at hab
      omega
  let C₁ : language_collection := {K | ∃ N : Nat, tail N ⊆ K.carrier}
  let C₂ : language_collection := {K | Set.range neg ⊆ K.carrier}
  refine ⟨C₁, C₂, ?_, ?_, ?_⟩
  · refine ⟨pos, ?_⟩
    rintro K ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro t ht
    constructor
    · exact hN ⟨t - N, by simp [tail, pos]; omega⟩
    · rintro ⟨i, hi, hEq⟩
      simp [pos] at hEq
      omega
  · refine ⟨neg, 0, ?_⟩
    intro K hK t ht
    constructor
    · exact hK ⟨t, rfl⟩
    · rintro ⟨i, hi, hEq⟩
      simp [neg] at hEq
      omega
  · intro hG
    rcases hG with ⟨G, hG⟩
    let IList (s : List Int) : Prop :=
      ∀ a b (ha : a < s.length) (hb : b < s.length), s[a] = s[b] → a = b
    let Good (n : Nat) (p : List Int × Nat) : Prop :=
      IList p.1 ∧
        (∀ u ∈ p.1, u ∉ tail p.2) ∧
        n ≤ p.1.length ∧
        (∀ m : Nat, neg m ∈ p.1 ↔ m < n)
    have advance (n : Nat) (p : List Int × Nat) (hp : Good n p) :
        ∃ p' : List Int × Nat, Good (n + 1) p' ∧ p.1 <+: p'.1 ∧ p.2 < p'.2 ∧
          (∀ u ∈ p'.1, u ∈ Set.range (enum p.1 p.2) ∨ u = neg n) ∧
          ∃ q ≥ p.1.length,
            ∃ k < p'.2, G (enumeration_prefix (enum p.1 p.2) q) = pos k ∧ pos k ∉ p'.1 ∧
              enumeration_prefix (enum p.1 p.2) q <+: p'.1 := by
      rcases hp with ⟨hp_inj, hp_dis, hp_len, hp_neg⟩
      have heinj := enum_injective p.1 p.2 hp_inj hp_dis
      let K : generation_language :=
        { carrier := Set.range (enum p.1 p.2)
          infinite_carrier := range_infinite heinj }
      have hKC₁ : K ∈ C₁ := by
        refine ⟨p.2, ?_⟩
        rintro u ⟨j, rfl⟩
        refine ⟨p.1.length + j, ?_⟩
        have hj : ¬p.1.length + j < p.1.length := by omega
        simp [enum, hj]
      have henum : enumerates_language (enum p.1 p.2) K := rfl
      rcases hG K (Or.inl hKC₁) (enum p.1 p.2) henum with ⟨t₀, ht₀⟩
      let q := max t₀ p.1.length
      have hq₀ : q ≥ t₀ := Nat.le_max_left _ _
      have hq₁ : q ≥ p.1.length := Nat.le_max_right _ _
      have hfresh := ht₀ q hq₀
      let y := G (enumeration_prefix (enum p.1 p.2) q)
      have hyK : y ∈ K.carrier := hfresh.1
      have hynot : y ∉ seen_prefix (enum p.1 p.2) q := hfresh.2
      rcases hyK with ⟨j, hj⟩
      have hjlarge : p.1.length ≤ j := by
        by_contra hlt
        have hjlt : j < p.1.length := by omega
        apply hynot
        refine ⟨j, ?_, ?_⟩
        · omega
        · simpa [y, enum, hjlt] using hj
      let k := p.2 + (j - p.1.length)
      have hypos : y = pos k := by simpa [y, k, enum, show ¬j < p.1.length by omega] using hj.symm
      let s' := enumeration_prefix (enum p.1 p.2) q ++ [neg n]
      let N' := max (p.2 + q + 1) (k + 1)
      have hprelen : (enumeration_prefix (enum p.1 p.2) q).length = q + 1 := by
        simp [enumeration_prefix]
      have hpreget (i : Nat) (hi : i < (enumeration_prefix (enum p.1 p.2) q).length) :
          (enumeration_prefix (enum p.1 p.2) q)[i] = enum p.1 p.2 i := by
        cases i with
        | zero => simp [enumeration_prefix]
        | succ i => simp [enumeration_prefix]
      have hneg_not : neg n ∉ Set.range (enum p.1 p.2) := by
        rintro ⟨i, hi⟩
        by_cases his : i < p.1.length
        · have hm : neg n ∈ p.1 := by
            rw [← hi]
            simpa [enum, his] using (List.getElem_mem p.1 i his)
          exact (hp_neg n).not.mpr (by omega) hm
        · dsimp [enum, neg, pos] at hi
          simp [his] at hi
          nomatch hi
      have hy_not_pre : y ∉ enumeration_prefix (enum p.1 p.2) q := by
        intro hy
        rcases List.mem_iff_getElem.mp hy with ⟨i, hi, hiy⟩
        apply hynot
        refine ⟨i, ?_, ?_⟩
        · rw [hprelen] at hi
          omega
        · simpa [hpreget i hi] using hiy
      refine ⟨(s', N'), ?_, ?_, ?_, ?_, q, hq₁, k, ?_, ?_, ?_, ?_⟩
      · dsimp [Good]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro a b ha hb hab
          have haBound : a ≤ (enumeration_prefix (enum p.1 p.2) q).length := by
            simp [s', hprelen] at ha
            omega
          have hbBound : b ≤ (enumeration_prefix (enum p.1 p.2) q).length := by
            simp [s', hprelen] at hb
            omega
          rcases Nat.eq_or_lt_of_le haBound with haEq | haLt
          · rcases Nat.eq_or_lt_of_le hbBound with hbEq | hbLt
            · omega
            · subst a
              exfalso
              apply hneg_not
              refine ⟨b, ?_⟩
              have hgb : s'[b] = enum p.1 p.2 b := by
                dsimp [s']
                simpa [List.getElem_append, hbLt] using hpreget b hbLt
              have hga : s'[(enumeration_prefix (enum p.1 p.2) q).length] = neg n := by
                simp [s']
              simpa [hgb, hga] using hab.symm
          · rcases Nat.eq_or_lt_of_le hbBound with hbEq | hbLt
            · subst b
              exfalso
              apply hneg_not
              refine ⟨a, ?_⟩
              have hga : s'[a] = enum p.1 p.2 a := by
                dsimp [s']
                simpa [List.getElem_append, haLt] using hpreget a haLt
              have hgb : s'[(enumeration_prefix (enum p.1 p.2) q).length] = neg n := by
                simp [s']
              simpa [hga, hgb] using hab
            · apply heinj
              have hga : s'[a] = enum p.1 p.2 a := by
                dsimp [s']
                simpa [List.getElem_append, haLt] using hpreget a haLt
              have hgb : s'[b] = enum p.1 p.2 b := by
                dsimp [s']
                simpa [List.getElem_append, hbLt] using hpreget b hbLt
              simpa [hga, hgb] using hab
        · intro u hu huTail
          dsimp [s'] at hu
          rcases List.mem_append.mp hu with hu | hu
          · rcases List.mem_iff_getElem.mp hu with ⟨i, hi, rfl⟩
            rw [hpreget i hi] at huTail
            rcases huTail with ⟨r, hr⟩
            by_cases his : i < p.1.length
            · have hold := hp_dis p.1[i] (List.getElem_mem ..)
              apply hold
              refine ⟨N' + r - p.2, ?_⟩
              calc
                pos (p.2 + (N' + r - p.2)) = pos (N' + r) := by
                  simp [pos]
                  dsimp [N']
                  omega
                _ = p.1[i] := by simpa [enum, his] using hr
            · simp [enum, his, pos] at hr
              rw [hprelen] at hi
              dsimp [N'] at hr
              omega
          · have huEq : u = neg n := by
              cases hu with
              | head => rfl
              | tail _ h => contradiction
            subst u
            rcases huTail with ⟨r, hr⟩
            dsimp [neg, pos] at hr
            nomatch hr
        · simp [s', enumeration_prefix]
          omega
        · intro m
          constructor
          · intro hm
            dsimp [s'] at hm
            rcases List.mem_append.mp hm with hm | hm
            · rcases List.mem_iff_getElem.mp hm with ⟨i, hi, hmi⟩
              have hmRange : neg m ∈ Set.range (enum p.1 p.2) := by
                exact ⟨i, by simpa [hpreget i hi] using hmi⟩
              rcases hmRange with ⟨i, hi⟩
              by_cases his : i < p.1.length
              · have : neg m ∈ p.1 := by
                  rw [← hi]
                  simp [enum, his]
                have := (hp_neg m).mp this
                omega
              · dsimp [enum, neg, pos] at hi
                simp [his] at hi
                nomatch hi
            · have : m = n := by
                cases hm with
                | head => rfl
                | tail _ h => contradiction
              omega
          · intro hm
            by_cases hmn : m = n
            · subst m
              apply List.mem_append.mpr
              exact Or.inr (by simp)
            · have hmold : m < n := by omega
              have hold := (hp_neg m).mpr hmold
              rcases List.mem_iff_getElem.mp hold with ⟨i, hi, him⟩
              apply List.mem_append.mpr
              apply Or.inl
              apply List.mem_iff_getElem.mpr
              refine ⟨i, ?_, ?_⟩
              · rw [hprelen]
                omega
              · rw [hpreget i (by rw [hprelen]; omega)]
                simpa [enum, hi] using him
      · dsimp [s']
        let r := enumeration_prefix (enum p.1 p.2) q
        have htake : List.take p.1.length r = p.1 := by
          apply List.ext_get
          · simp [r, hprelen]
            omega
          · intro i h₁ h₂
            simp [r, hpreget i (by rw [hprelen]; omega), enum, h₂]
        refine ⟨List.drop p.1.length r ++ [neg n], ?_⟩
        calc
          p.1 ++ (List.drop p.1.length r ++ [neg n]) =
              (p.1 ++ List.drop p.1.length r) ++ [neg n] := by rw [List.append_assoc]
          _ = (List.take p.1.length r ++ List.drop p.1.length r) ++ [neg n] := by rw [htake]
          _ = r ++ [neg n] := by rw [List.take_append_drop]
      · dsimp [N']
        omega
      · intro u hu
        dsimp [s'] at hu
        rcases List.mem_append.mp hu with hu | hu
        · left
          rcases List.mem_iff_getElem.mp hu with ⟨i, hi, hEq⟩
          exact ⟨i, by simpa [hpreget i hi] using hEq⟩
        · right
          cases hu with
          | head => rfl
          | tail _ h => contradiction
      · dsimp [N']
        omega
      · simpa [y] using hypos
      · change pos k ∉ s'
        intro hk
        dsimp [s'] at hk
        rcases List.mem_append.mp hk with hk | hk
        · exact hy_not_pre (by simpa [hypos] using hk)
        · have hEq : y = neg n := by simpa using hk
          rw [hypos] at hEq
          dsimp [pos, neg] at hEq
          nomatch hEq
      · exact ⟨[neg n], rfl⟩
    have hbase : Good 0 ([], 0) := by
      simp [Good, IList]
    let next (n : Nat) (p : {p : List Int × Nat // Good n p}) :
        {p : List Int × Nat // Good (n + 1) p} :=
      ⟨Classical.choose (advance n p.1 p.2),
        (Classical.choose_spec (advance n p.1 p.2)).1⟩
    let st : (n : Nat) → {p : List Int × Nat // Good n p} := fun n =>
      Nat.rec ⟨([], 0), hbase⟩ (fun n p => next n p) n
    have st_succ (n : Nat) : st (n + 1) = next n (st n) := by rfl
    have st_good (n : Nat) : Good n (st n).1 := (st n).2
    have st_prefix (n : Nat) : (st n).1.1 <+: (st (n + 1)).1.1 := by
      rw [st_succ]
      exact (Classical.choose_spec (advance n (st n).1 (st n).2)).2.1
    have st_bound_step (n : Nat) : (st n).1.2 < (st (n + 1)).1.2 := by
      rw [st_succ]
      exact (Classical.choose_spec (advance n (st n).1 (st n).2)).2.2.1
    have st_containment (n : Nat) :
        ∀ u ∈ (st (n + 1)).1.1,
          u ∈ Set.range (enum (st n).1.1 (st n).1.2) ∨ u = neg n := by
      rw [st_succ]
      exact (Classical.choose_spec (advance n (st n).1 (st n).2)).2.2.2.1
    have prefix_trans {a b c : List Int} (hab : a <+: b) (hbc : b <+: c) : a <+: c := by
      rcases hab with ⟨u, rfl⟩
      rcases hbc with ⟨v, hv⟩
      refine ⟨u ++ v, ?_⟩
      simpa [List.append_assoc] using hv
    have st_prefix_add (n d : Nat) : (st n).1.1 <+: (st (n + d)).1.1 := by
      induction d with
      | zero => exact ⟨[], by simp⟩
      | succ d ih =>
          apply prefix_trans ih
          have hEq : n + (d + 1) = (n + d) + 1 := by omega
          rw [hEq]
          exact st_prefix (n + d)
    have st_prefix_le {n m : Nat} (h : n ≤ m) : (st n).1.1 <+: (st m).1.1 := by
      have hEq : n + (m - n) = m := by omega
      rw [← hEq]
      exact st_prefix_add n (m - n)
    have prefix_get {a b : List Int} (hab : a <+: b) (i : Nat) (hi : i < a.length) :
        a[i] = b[i]'(by rcases hab with ⟨r, rfl⟩; simp; omega) := by
      rcases hab with ⟨r, rfl⟩
      simp [List.getElem_append, hi]
    let x : Nat → Int := fun i =>
      (st (i + 1)).1.1[i]'(by
        have hlen := (st_good (i + 1)).2.2.1
        omega)
    have x_injective : Function.Injective x := by
      intro a b hab
      let m := max (a + 1) (b + 1)
      have haM : a + 1 ≤ m := Nat.le_max_left _ _
      have hbM : b + 1 ≤ m := Nat.le_max_right _ _
      have hpa := st_prefix_le haM
      have hpb := st_prefix_le hbM
      have haLen : a < (st (a + 1)).1.1.length := by
        have := (st_good (a + 1)).2.2.1
        omega
      have hbLen : b < (st (b + 1)).1.1.length := by
        have := (st_good (b + 1)).2.2.1
        omega
      have haEq := prefix_get hpa a haLen
      have hbEq := prefix_get hpb b hbLen
      have hinjM := (st_good m).1
      dsimp [IList] at hinjM
      have haLm : a < (st m).1.1.length := by
        have := (st_good m).2.2.1
        omega
      have hbLm : b < (st m).1.1.length := by
        have := (st_good m).2.2.1
        omega
      apply hinjM a b haLm hbLm
      rw [← haEq, ← hbEq]
      simpa [x] using hab
    let Kstar : generation_language :=
      { carrier := Set.range x
        infinite_carrier := range_infinite x_injective }
    have hKstarC₂ : Kstar ∈ C₂ := by
      rintro u ⟨n, rfl⟩
      have hnmem : neg n ∈ (st (n + 1)).1.1 :=
        ((st_good (n + 1)).2.2.2 n).mpr (by omega)
      rcases List.mem_iff_getElem.mp hnmem with ⟨i, hi, hEq⟩
      refine ⟨i, ?_⟩
      dsimp [x]
      by_cases hle : i + 1 ≤ n + 1
      · have hp := st_prefix_le hle
        have hxi : i < (st (i + 1)).1.1.length := by
          have := (st_good (i + 1)).2.2.1
          omega
        rw [prefix_get hp i hxi]
        exact hEq
      · have hp := st_prefix_le (show n + 1 ≤ i + 1 by omega)
        have hni : i < (st (n + 1)).1.1.length := hi
        rw [← prefix_get hp i hni]
        exact hEq
    have hKenum : enumerates_language x Kstar := rfl
    rcases hG Kstar (Or.inr hKstarC₂) x hKenum with ⟨T, hT⟩
    have st_data (n : Nat) :
        ∃ q ≥ (st n).1.1.length, ∃ k < (st (n + 1)).1.2,
          G (enumeration_prefix (enum (st n).1.1 (st n).1.2) q) = pos k ∧
            pos k ∉ (st (n + 1)).1.1 ∧
            enumeration_prefix (enum (st n).1.1 (st n).1.2) q <+: (st (n + 1)).1.1 := by
      rw [st_succ]
      exact (Classical.choose_spec (advance n (st n).1 (st n).2)).2.2.2.2
    rcases st_data T with ⟨q, hq, k, hkN, hGq, hklist, hpre⟩
    have hqT : T ≤ q := by
      have := (st_good T).2.2.1
      omega
    have absent_enum (m r : Nat) (hrN : r < (st m).1.2)
        (hrlist : pos r ∉ (st m).1.1) :
        pos r ∉ Set.range (enum (st m).1.1 (st m).1.2) := by
      rintro ⟨i, hi⟩
      by_cases his : i < (st m).1.1.length
      · apply hrlist
        rw [← hi]
        simpa [enum, his] using (List.getElem_mem (st m).1.1 i his)
      · simp [enum, pos, his] at hi
        omega
    have absent_states (d : Nat) :
        k < (st (T + 1 + d)).1.2 ∧ pos k ∉ (st (T + 1 + d)).1.1 := by
      induction d with
      | zero => simpa using And.intro hkN hklist
      | succ d ih =>
          have hindex : T + 1 + (d + 1) = (T + 1 + d) + 1 := by omega
          rw [hindex]
          constructor
          · have hs := st_bound_step (T + 1 + d)
            omega
          · intro hmem
            rcases st_containment (T + 1 + d) (pos k) hmem with hprev | hneg
            · exact absent_enum (T + 1 + d) k ih.1 ih.2 hprev
            · dsimp [pos, neg] at hneg
              nomatch hneg
    have hkK : pos k ∉ Kstar.carrier := by
      rintro ⟨i, hi⟩
      let m := max (T + 1) (i + 1)
      have hTi : T + 1 ≤ m := Nat.le_max_left _ _
      have hii : i + 1 ≤ m := Nat.le_max_right _ _
      have hmEq : T + 1 + (m - (T + 1)) = m := by omega
      have habs := absent_states (m - (T + 1))
      rw [hmEq] at habs
      apply habs.2
      have hp := st_prefix_le hii
      have hilen : i < (st (i + 1)).1.1.length := by
        have := (st_good (i + 1)).2.2.1
        omega
      apply List.mem_iff_getElem.mpr
      refine ⟨i, ?_, ?_⟩
      · have := (st_good m).2.2.1
        omega
      · rw [← prefix_get hp i hilen]
        simpa [Kstar, x] using hi
    have hprefixEq : enumeration_prefix x q =
        enumeration_prefix (enum (st T).1.1 (st T).1.2) q := by
      apply List.ext_get
      · simp [enumeration_prefix]
      · intro i hi₁ hi₂
        have hiq : i < (enumeration_prefix (enum (st T).1.1 (st T).1.2) q).length := by
          exact hi₂
        have hxget : (enumeration_prefix x q)[i] = x i := by
          cases i with
          | zero => simp [enumeration_prefix]
          | succ i => simp [enumeration_prefix]
        have heget :
            (enumeration_prefix (enum (st T).1.1 (st T).1.2) q)[i] =
              enum (st T).1.1 (st T).1.2 i := by
          cases i with
          | zero => simp [enumeration_prefix]
          | succ i => simp [enumeration_prefix]
        have hstage := prefix_get hpre i hiq
        change (enumeration_prefix x q)[i] =
          (enumeration_prefix (enum (st T).1.1 (st T).1.2) q)[i]
        rw [hxget, heget]
        by_cases hle : i + 1 ≤ T + 1
        · have hp := st_prefix_le hle
          have hil : i < (st (i + 1)).1.1.length := by
            have := (st_good (i + 1)).2.2.1
            omega
          have hstable := prefix_get hp i hil
          dsimp [x]
          exact hstable.trans (by simpa [heget] using hstage.symm)
        · have hp := st_prefix_le (show T + 1 ≤ i + 1 by omega)
          have hTl : i < (st (T + 1)).1.1.length := by
            have hlen := hpre.length_le
            have hqLen : i < q + 1 := by
              simpa [enumeration_prefix] using hiq
            have hpreLen :
                (enumeration_prefix (enum (st T).1.1 (st T).1.2) q).length = q + 1 := by
              simp [enumeration_prefix]
            rw [hpreLen] at hlen
            omega
          have hstable := prefix_get hp i hTl
          dsimp [x]
          exact hstable.symm.trans (by simpa [heget] using hstage.symm)
    have hfresh := hT q hqT
    apply hkK
    rw [← hGq, ← hprefixEq]
    exact hfresh.1

@[blueprint "thm:union-ungen"
  (statement := /-- There exist collections \(\mathcal C_1\) and
  \(\mathcal C_2\) such that \(\mathcal C_1\) is non-uniformly generatable
  without samples and \(\mathcal C_2\) is uniformly generatable without
  samples, whereas \(\mathcal C_1\cup\mathcal C_2\) is not generatable in the
  limit. -/)
  (proof := /-- Choose \(\mathcal C_1,\mathcal C_2\) as supplied by
  \cref{lem:separating-collections-exist}.  Unfolding the separation package
  in \cref{def:separating-collections} gives, respectively, non-uniform
  sample-free generation of \(\mathcal C_1\), uniform sample-free generation
  of \(\mathcal C_2\), and failure of generation in the limit for
  \(\mathcal C_1\cup\mathcal C_2\), which are precisely the three asserted
  properties. -/)
  (title := /-- Union of generatable collections need not be generatable -/)
  (latexEnv := "theorem")]
theorem union_ungen :
    ∃ C₁ C₂ : language_collection,
      nonuniformly_generatable_without_samples C₁ ∧
      uniformly_generatable_without_samples C₂ ∧
      ¬ generatable_in_limit (C₁ ∪ C₂) := by
  simpa [separating_collections] using separating_collections_exist

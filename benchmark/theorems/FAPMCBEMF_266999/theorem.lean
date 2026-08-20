import Mathlib

def cut_value {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, w u v

def weighted_degree {V : Type*} [Fintype V] (w : V → V → ℝ) (v : V) : ℝ :=
  ∑ u, w v u

def crossing_weight {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then ∑ u ∈ Sᶜ, w v u else ∑ u ∈ S, w v u

noncomputable def friendliness_ratio {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (S : Finset V) (v : V) : ℝ :=
  1 - crossing_weight w S v / weighted_degree w v

def is_friendly_cut {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (α : ℝ) (S : Finset V) : Prop :=
  ∀ v : V, α ≤ friendliness_ratio w S v

def contracted_graph {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (w : V → V → ℝ) (π : V → W) : W → W → ℝ :=
  fun a b =>
    if a = b then 0
    else ∑ u ∈ Finset.univ.filter (fun u => π u = a),
          ∑ v ∈ Finset.univ.filter (fun v => π v = b), w u v

def has_connected_contraction_fibres {V W : Type*} (w : V → V → ℝ) (π : V → W) : Prop :=
  ∀ u v : V, π u = π v →
    Relation.ReflTransGen (fun x y : V => w x y ≠ 0 ∨ w y x ≠ 0) u v

structure friendly_sparsifier_access (V W : Type*) where
  projection : V → W
  edgeWeights : V → V → ℝ

def is_friendly_sparsifier_access {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (α budget : ℝ) (w : V → V → ℝ)
    (Hfr : friendly_sparsifier_access V W) : Prop :=
  Function.Surjective Hfr.projection ∧
    has_connected_contraction_fibres w Hfr.projection ∧
    (∀ u v : V, Hfr.edgeWeights u v =
      if Hfr.projection u = Hfr.projection v then 0 else w u v) ∧
    ∀ S : Finset V, is_friendly_cut w α S → cut_value w S ≤ budget →
      (∀ u v : V, Hfr.projection u = Hfr.projection v → (u ∈ S ↔ v ∈ S)) ∧
        cut_value (contracted_graph Hfr.edgeWeights Hfr.projection) (S.image Hfr.projection) =
          cut_value w S

noncomputable def min_st_cut_value {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (s t : V) : ℝ :=
  sInf ((fun S => cut_value w S) '' {S : Finset V | s ∈ S ∧ t ∉ S})

def is_min_st_cut {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ)
    (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S ∧ cut_value w S = min_st_cut_value w s t

def is_apmc_sparsifier {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (w : V → V → ℝ) (ι : V → U) (H : U → U → ℝ) : Prop :=
  Function.Injective ι ∧
    ∀ s t : V, s ≠ t → ∃ S : Finset U,
      is_min_st_cut H (ι s) (ι t) S ∧
      is_min_st_cut w s t (Finset.univ.filter (fun v : V => ι v ∈ S)) ∧
      cut_value H S = cut_value w (Finset.univ.filter (fun v : V => ι v ∈ S)) ∧
      min_st_cut_value H (ι s) (ι t) = min_st_cut_value w s t

noncomputable def edge_count {U : Type*} [Fintype U] (H : U → U → ℝ) : ℕ :=
  {e : Sym2 U |
      ¬ e.IsDiag ∧ Sym2.lift ⟨fun a b => H a b ≠ 0 ∨ H b a ≠ 0, fun _ _ => propext or_comm⟩ e}.ncard

structure costed_apmc_constructor (V W : Type*) where
  run : friendly_sparsifier_access V W → (V → ℝ) → (V ⊕ W) → (V ⊕ W) → ℝ
  runningTime : friendly_sparsifier_access V W → (V → ℝ) → ℕ

def is_linear_time_apmc_construction {V W : Type*} [Fintype V]
    (A : costed_apmc_constructor V W) : Prop :=
  ∃ C : ℕ, 0 < C ∧
    ∀ (Hfr : friendly_sparsifier_access V W) (degrees : V → ℝ),
      A.runningTime Hfr degrees ≤ C * (edge_count Hfr.edgeWeights + Fintype.card V)

def is_simple_unweighted_graph {V : Type*} (w : V → V → ℝ) : Prop :=
  (∀ u v, w u v = w v u) ∧ (∀ v, w v v = 0) ∧ (∀ u v : V, w u v = 0 ∨ w u v = 1)

theorem apmc_sparsifier_construction
    {V : Type*} [Fintype V] [DecidableEq V]
    {Wv : Type*} [Fintype Wv] [DecidableEq Wv] :
    ∃ A : costed_apmc_constructor V Wv,
      is_linear_time_apmc_construction A ∧
      ∀ (w : V → V → ℝ) (hG : is_simple_unweighted_graph w)
        (Hfr : friendly_sparsifier_access V Wv)
        (hfr : is_friendly_sparsifier_access
          (1 / 6) (2 * (Fintype.card V : ℝ)) w Hfr)
        (hdeg : ∀ v : V, weighted_degree w v ≠ 1),
        is_apmc_sparsifier w Sum.inl (A.run Hfr (weighted_degree w)) ∧
          edge_count (A.run Hfr (weighted_degree w)) ≤
            edge_count Hfr.edgeWeights + Fintype.card V := by sorry

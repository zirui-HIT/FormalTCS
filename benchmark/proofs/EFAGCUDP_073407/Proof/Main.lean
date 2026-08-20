import Architect
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Order.Compact

set_option linter.all false
set_option maxHeartbeats 500000

open scoped BigOperators

@[blueprint "def:fair-goods-instance"
  (statement := /-- A finite goods instance consists of finitely many groups and item types, a positive-integer group-size function, a nonnegative additive value for each group and item type, a copy count for each item type, and distinguished smallest and largest groups. -/)
  (title := /-- Finite grouped goods instance -/)
  (latexEnv := "definition")]
structure fair_goods_instance (Group ItemType : Type*) where
  groupSize : Group → ℕ
  valuation : Group → ItemType → ℝ
  copies : ItemType → ℕ
  smallestGroup : Group
  largestGroup : Group
  someType : ItemType

@[blueprint "def:number-of-groups"
  (statement := /-- The number of groups is the cardinality of the finite group type. -/)
  (title := /-- Number of groups -/)
  (latexEnv := "definition")]
def number_of_groups {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  Fintype.card Group

@[blueprint "def:number-of-types"
  (statement := /-- The number of item types is the cardinality of the finite item-type space. -/)
  (title := /-- Number of item types -/)
  (latexEnv := "definition")]
def number_of_types {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  Fintype.card ItemType

@[blueprint "def:number-of-agents"
  (statement := /-- The total number of agents is the sum of the sizes of all groups. -/)
  (title := /-- Total number of agents -/)
  (latexEnv := "definition")]
def number_of_agents {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  ∑ i, I.groupSize i

@[blueprint "def:group-size-gcd"
  (statement := /-- The integer $g$ is the greatest common divisor of the sizes of all groups. -/)
  (title := /-- Greatest common divisor of group sizes -/)
  (latexEnv := "definition")]
def group_size_gcd {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  Finset.univ.gcd I.groupSize

@[blueprint "def:frobenius-threshold"
  (statement := /-- With $g$ the gcd of the group sizes, $n_1$ the distinguished smallest group size, and $n_d$ the distinguished largest group size, define
  \[
    \theta=g\left(\frac{n_1}{g}-1\right)\left(\frac{n_d}{g}-1\right).
  \] -/)
  (title := /-- Frobenius--Brauer threshold -/)
  (latexEnv := "definition")]
def frobenius_threshold {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  group_size_gcd I * (I.groupSize I.smallestGroup / group_size_gcd I - 1) *
    (I.groupSize I.largestGroup / group_size_gcd I - 1)

@[blueprint "def:goods-profile-assumptions"
  (statement := /-- A goods profile is admissible when every group is nonempty, the distinguished extremal groups have the asserted order properties, every value is nonnegative, every group's unit-copy valuation vector has positive Euclidean norm, at least two distinct groups exist, and the unit-copy normalized valuation vectors of every two distinct groups have strictly positive squared Euclidean distance. -/)
  (title := /-- Admissible grouped valuation profile -/)
  (latexEnv := "definition")]
def goods_profile_assumptions {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : Prop :=
  (∀ i, 0 < I.groupSize i) ∧
    (∀ i, I.groupSize I.smallestGroup ≤ I.groupSize i) ∧
    (∀ i, I.groupSize i ≤ I.groupSize I.largestGroup) ∧
    (∀ i z, 0 ≤ I.valuation i z) ∧
    (∀ i, 0 < Real.sqrt (∑ z, (I.valuation i z) ^ 2)) ∧
    (∃ i i' : Group, i ≠ i') ∧
    (∀ i i', i ≠ i' →
      0 < ∑ z,
        (I.valuation i z / Real.sqrt (∑ w, (I.valuation i w) ^ 2) -
          I.valuation i' z / Real.sqrt (∑ w, (I.valuation i' w) ^ 2)) ^ 2)

@[blueprint "def:unit-valuation-norm"
  (statement := /-- The unit-copy Euclidean norm of group $i$'s valuation vector is
  $\left(\sum_z v_{i,z}^2\right)^{1/2}$. -/)
  (title := /-- Unit-copy valuation norm -/)
  (latexEnv := "definition")]
noncomputable def unit_valuation_norm {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i : Group) : ℝ :=
  Real.sqrt (∑ z, (I.valuation i z) ^ 2)

@[blueprint "def:unit-normalized-value"
  (statement := /-- The unit-copy normalized value of item type $z$ for group $i$ is $v_{i,z}/\lVert v_i\rVert_2$. -/)
  (title := /-- Unit-copy normalized valuation -/)
  (latexEnv := "definition")]
noncomputable def unit_normalized_value {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i : Group) (z : ItemType) : ℝ :=
  I.valuation i z / unit_valuation_norm I i

@[blueprint "def:unit-separation-squared"
  (statement := /-- The squared unit-copy normalized separation of groups $i$ and $i'$ is
  $\sum_z(\widetilde v_{i,z}-\widetilde v_{i',z})^2$. -/)
  (title := /-- Squared normalized separation -/)
  (latexEnv := "definition")]
noncomputable def unit_separation_squared {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i i' : Group) : ℝ :=
  ∑ z, (unit_normalized_value I i z - unit_normalized_value I i' z) ^ 2

@[blueprint "def:minimum-unit-separation-squared"
  (statement := /-- The minimum squared normalized separation is the minimum of
  $\lVert\widetilde v_i-\widetilde v_{i'}\rVert_2^2$ over all ordered pairs $(i,i')$ of distinct groups. It is defined to be zero only when no such pair exists. -/)
  (title := /-- Minimum unit-copy normalized separation -/)
  (latexEnv := "definition")]
noncomputable def minimum_unit_separation_squared {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType) : ℝ := by
  classical
  let pairs : Finset (Group × Group) :=
    (Finset.univ.product Finset.univ).filter (fun p => p.1 ≠ p.2)
  exact if h : pairs.Nonempty then
    pairs.inf' h (fun p => unit_separation_squared I p.1 p.2)
  else 0

@[blueprint "def:copy-weighted-valuation-norm"
  (statement := /-- For the copy vector $\mathbf k$, the Euclidean norm of group $i$'s expanded valuation vector is
  $\left(\sum_z k_zv_{i,z}^2\right)^{1/2}$. -/)
  (title := /-- Copy-weighted valuation norm -/)
  (latexEnv := "definition")]
noncomputable def copy_weighted_valuation_norm {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i : Group) : ℝ :=
  Real.sqrt (∑ z, (I.copies z : ℝ) * (I.valuation i z) ^ 2)

@[blueprint "def:copy-weighted-normalized-value"
  (statement := /-- The normalized value of one copy of type $z$ in the expanded instance is $v_{i,z}/\lVert v_i(\mathbf k)\rVert_2$. -/)
  (title := /-- Copy-weighted normalized value -/)
  (latexEnv := "definition")]
noncomputable def copy_weighted_normalized_value {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i : Group) (z : ItemType) : ℝ :=
  I.valuation i z / copy_weighted_valuation_norm I i

@[blueprint "def:copy-weighted-separation-squared"
  (statement := /-- The squared distance between the expanded normalized valuation vectors of $i$ and $i'$ is
  $\sum_z k_z(\widetilde v_{i,z}(\mathbf k)-\widetilde v_{i',z}(\mathbf k))^2$. -/)
  (title := /-- Copy-weighted normalized separation -/)
  (latexEnv := "definition")]
noncomputable def copy_weighted_separation_squared {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i i' : Group) : ℝ :=
  ∑ z, (I.copies z : ℝ) *
    (copy_weighted_normalized_value I i z - copy_weighted_normalized_value I i' z) ^ 2

@[blueprint "def:minimum-copy-weighted-separation-squared"
  (statement := /-- The minimum expanded squared separation is the minimum over all ordered pairs of distinct groups. It is defined to be zero only when no such pair exists. -/)
  (title := /-- Minimum copy-weighted normalized separation -/)
  (latexEnv := "definition")]
noncomputable def minimum_copy_weighted_separation_squared {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType) : ℝ := by
  classical
  let pairs : Finset (Group × Group) :=
    (Finset.univ.product Finset.univ).filter (fun p => p.1 ≠ p.2)
  exact if h : pairs.Nonempty then
    pairs.inf' h (fun p => copy_weighted_separation_squared I p.1 p.2)
  else 0

@[blueprint "def:maximum-copy-normalized-item-value"
  (statement := /-- The quantity $\widetilde v_{\max}(\mathbf k)$ is the maximum normalized value of a single copy over all groups and item types. -/)
  (title := /-- Maximum normalized single-copy value -/)
  (latexEnv := "definition")]
noncomputable def maximum_copy_normalized_item_value {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType) : ℝ := by
  classical
  exact (Finset.univ.product Finset.univ).sup'
    ⟨(I.smallestGroup, I.someType), by simp⟩
    (fun p => copy_weighted_normalized_value I p.1 p.2)

@[blueprint "def:maximum-item-value"
  (statement := /-- For a group $i$, the maximum value of a single item type is $\max_z v_{i,z}$. -/)
  (title := /-- Maximum value of one item -/)
  (latexEnv := "definition")]
noncomputable def maximum_item_value {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (i : Group) : ℝ := by
  classical
  exact Finset.univ.sup' ⟨I.someType, by simp⟩ (I.valuation i)

@[blueprint "def:rounding-complexity"
  (statement := /-- The loss term in the rounding theorem is
  $d(d-1)+t(\theta+n+n_d-d-1)$. -/)
  (title := /-- Rounding loss parameter -/)
  (latexEnv := "definition")]
def rounding_complexity {Group ItemType : Type*} [Fintype Group] [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  number_of_groups I * (number_of_groups I - 1) +
    number_of_types I * (frobenius_threshold I + number_of_agents I +
      I.groupSize I.largestGroup - number_of_groups I - 1)

@[blueprint "def:advertised-copy-complexity"
  (statement := /-- The numerator's combinatorial factor in the advertised theorem is
  $d^2+t(\theta+n+n_d-d-1)$. -/)
  (title := /-- Advertised copy-bound parameter -/)
  (latexEnv := "definition")]
def advertised_copy_complexity {Group ItemType : Type*} [Fintype Group] [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : ℕ :=
  number_of_groups I ^ 2 +
    number_of_types I * (frobenius_threshold I + number_of_agents I +
      I.groupSize I.largestGroup - number_of_groups I - 1)

@[blueprint "def:advertised-copy-lower-bound"
  (statement := /-- Define
  \[
    \mu=\frac{4n\bigl(d^2+t(\theta+n+n_d-d-1)\bigr)}
    {\min_{i\ne i'}\lVert\widetilde v_i-\widetilde v_{i'}\rVert_2^2}.
  \]
  The denominator is the minimum over ordered pairs of distinct groups. -/)
  (title := /-- Advertised lower bound on copies -/)
  (latexEnv := "definition")]
noncomputable def advertised_copy_lower_bound {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType) : ℝ :=
  ((4 * number_of_agents I * advertised_copy_complexity I : ℕ) : ℝ) /
    minimum_unit_separation_squared I

@[blueprint "def:allocation"
  (statement := /-- An allocation assigns to each group the integral bundle received by each individual member of that group. -/)
  (title := /-- Equal-within-group integral allocation -/)
  (latexEnv := "definition")]
def allocation (Group ItemType : Type*) :=
  Group → ItemType → ℕ

@[blueprint "def:bundle-value"
  (statement := /-- Group $i$'s additive value for the per-agent bundle assigned to group $i'$ is $\sum_zv_{i,z}A_{i',z}$. -/)
  (title := /-- Additive value of a group bundle -/)
  (latexEnv := "definition")]
def bundle_value {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (A : allocation Group ItemType)
    (i i' : Group) : ℝ :=
  ∑ z, I.valuation i z * (A i' z : ℝ)

@[blueprint "def:complete-allocation"
  (statement := /-- An allocation is complete when, for each type $z$, the sum of the common per-agent bundle size multiplied by each group size equals the available copy count $k_z$. -/)
  (title := /-- Complete allocation -/)
  (latexEnv := "definition")]
def complete_allocation {Group ItemType : Type*} [Fintype Group]
    (I : fair_goods_instance Group ItemType) (A : allocation Group ItemType) : Prop :=
  ∀ z, ∑ i, I.groupSize i * A i z = I.copies z

@[blueprint "def:envy-free-allocation"
  (statement := /-- An allocation is envy-free when every group weakly prefers its own per-agent bundle to the per-agent bundle of every other group. -/)
  (title := /-- Envy-free allocation -/)
  (latexEnv := "definition")]
def envy_free_allocation {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (A : allocation Group ItemType) : Prop :=
  ∀ i i', bundle_value I A i i' ≤ bundle_value I A i i

@[blueprint "def:admits-envy-free-allocation"
  (statement := /-- An instance admits an envy-free allocation if it has a complete integral allocation, equal within every group, that is envy-free. -/)
  (title := /-- Existence of an envy-free allocation -/)
  (latexEnv := "definition")]
def admits_envy_free_allocation {Group ItemType : Type*} [Fintype Group] [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) : Prop :=
  ∃ A : allocation Group ItemType, complete_allocation I A ∧ envy_free_allocation I A

@[blueprint "def:instance-with-copies"
  (statement := /-- Replacing only the copy-count vector of an instance by $r$ leaves its groups, valuations, and distinguished indices unchanged. -/)
  (title := /-- Instance with a replaced copy vector -/)
  (latexEnv := "definition")]
def instance_with_copies {Group ItemType : Type*} (I : fair_goods_instance Group ItemType)
    (r : ItemType → ℕ) : fair_goods_instance Group ItemType :=
  { I with copies := r }

@[blueprint "def:copied-item"
  (statement := /-- A copied item is a pair $(z,s)$ consisting of an item type $z$ and an index $sin\{0,\ldots,k_z-1\}$. Thus distinct copies of the same type are represented separately. -/)
  (title := /-- Individually indexed copies -/)
  (latexEnv := "definition")]
abbrev copied_item {Group ItemType : Type*} (I : fair_goods_instance Group ItemType) :=
  Σ z : ItemType, Fin (I.copies z)

@[blueprint "def:fractional-allocation"
  (statement := /-- A fractional allocation assigns a nonnegative real fraction $x_{i,j}$ of each individually indexed copy $j$ to the common bundle of every agent in group $i$. Feasibility constraints are imposed separately in \cref{def:max-min-envy-gap-feasible-set}. -/)
  (title := /-- Fractional equal-within-group allocations -/)
  (latexEnv := "definition")]
def fractional_allocation {Group ItemType : Type*}
    (I : fair_goods_instance Group ItemType) :=
  Group → copied_item I → ℝ

@[blueprint "def:fractional-bundle-value"
  (statement := /-- For a fractional allocation $X$, the value assigned by group $i$ to the common fractional bundle of group $i'$ is
  $\sum_j v_{i,z(j)}X_{i',j}$, where $z(j)$ is the type of copy $j$. -/)
  (title := /-- Value of a fractional bundle -/)
  (latexEnv := "definition")]
def fractional_bundle_value {Group ItemType : Type*} [Fintype ItemType]
    (I : fair_goods_instance Group ItemType) (X : fractional_allocation I)
    (i i' : Group) : ℝ :=
  ∑ j, I.valuation i j.1 * X i' j

@[blueprint "def:max-min-envy-gap-feasible-set"
  (statement := /-- The max--min envy-gap feasible set consists of pairs $(X,\alpha)$ such that $X_{i,j}\ge0$, every copy is completely distributed according to
  $\sum_i n_iX_{i,j}=1$, and for every ordered pair of distinct groups,
  [
    \lVert v_i(\mathbf k)\rVert_2\alpha
      \le v_i(X_i)-v_i(X_{i'}).
  ]
  Maximizing the second coordinate is the source proof's finite-dimensional linear program. -/)
  (title := /-- Feasible set for the max--min envy-gap program -/)
  (latexEnv := "definition")]
def max_min_envy_gap_feasible_set {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType) :
    Set (fractional_allocation I × ℝ) :=
  {p | (∀ i j, 0 ≤ p.1 i j) ∧
    (∀ j, ∑ i, (I.groupSize i : ℝ) * p.1 i j = 1) ∧
    (∀ i i', i ≠ i' →
      copy_weighted_valuation_norm I i * p.2 ≤
        fractional_bundle_value I p.1 i i -
          fractional_bundle_value I p.1 i i')}

@[blueprint "def:shared-copied-items"
  (statement := /-- A copied item is shared by a fractional allocation when two distinct groups both receive a strictly positive fraction of it. The quantity $\operatorname{Shared}(X)$ is the cardinality of the finite type of all such copied items. -/)
  (title := /-- Number of fractionally shared copied items -/)
  (latexEnv := "definition")]
noncomputable def shared_copied_items {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (X : fractional_allocation I) : ℕ :=
  Nat.card {j : copied_item I //
    ∃ i i', i ≠ i' ∧ 0 < X i j ∧ 0 < X i' j}

@[blueprint "lem:relative-norm-fractional-allocation-feasible"
  (statement := /-- Let $I$ be an admissible finite goods profile with strictly positive copy counts. There is a feasible fractional allocation whose max--min gap coordinate is
  \[
    \frac{\delta(\mathbf k)^2}
      {2n\widetilde v_{\max}(\mathbf k)}.
  \] -/)
  (proof := /-- Define the allocation of a copied item of type $z$ to group $i$ by perturbing the uniform allocation in the direction of the difference between group $i$'s copy-normalized value of $z$ and its group-size-weighted average. The weighted perturbations sum to zero, so every copied item is completely allocated. Nonnegativity follows because all normalized values lie between zero and $\widetilde v_{\max}(\mathbf k)$. Expanding the gap between two distinct groups and using that both copy-normalized valuation vectors have squared norm one gives half their squared distance, which yields the displayed feasible gap. -/)
  (title := /-- Feasibility of the relative-norm fractional allocation -/)
  (latexEnv := "lemma")]
lemma relative_norm_fractional_allocation_feasible {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z) :
    ∃ X : fractional_allocation I,
      (X, minimum_copy_weighted_separation_squared I /
        (2 * (number_of_agents I : ℝ) *
          maximum_copy_normalized_item_value I)) ∈
        max_min_envy_gap_feasible_set I := by
  classical
  rcases hprofile with
    ⟨hsize, hsmallest, hlargest, hvalue, hunitnorm, hgroups, hunitsep⟩
  have hn_nat : 0 < number_of_agents I := by
    unfold number_of_agents
    exact Finset.sum_pos' (fun i _ => Nat.zero_le (I.groupSize i))
      ⟨I.smallestGroup, Finset.mem_univ _, hsize I.smallestGroup⟩
  have hn : 0 < (number_of_agents I : ℝ) := by
    exact_mod_cast hn_nat
  have hweighted_sum_pos (i : Group) :
      0 < ∑ z, (I.copies z : ℝ) * (I.valuation i z) ^ 2 := by
    have hu : 0 < ∑ z, (I.valuation i z) ^ 2 := by
      exact Real.sqrt_pos.mp (hunitnorm i)
    refine lt_of_lt_of_le hu (Finset.sum_le_sum fun z _ => ?_)
    have hc : (1 : ℝ) ≤ I.copies z := by
      exact_mod_cast hpositive z
    nlinarith [sq_nonneg (I.valuation i z)]
  have hcopy_norm (i : Group) : 0 < copy_weighted_valuation_norm I i := by
    rw [copy_weighted_valuation_norm]
    exact Real.sqrt_pos.mpr (hweighted_sum_pos i)
  have hnormalized_nonneg (i : Group) (z : ItemType) :
      0 ≤ copy_weighted_normalized_value I i z := by
    rw [copy_weighted_normalized_value]
    exact div_nonneg (hvalue i z) (le_of_lt (hcopy_norm i))
  have hsome_value_pos :
      ∃ z : ItemType, 0 < I.valuation I.smallestGroup z := by
    have hu : 0 < ∑ z, (I.valuation I.smallestGroup z) ^ 2 := by
      exact Real.sqrt_pos.mp (hunitnorm I.smallestGroup)
    obtain ⟨z, _, hz⟩ :=
      (Finset.sum_pos_iff_of_nonneg
        (fun z (_ : z ∈ (Finset.univ : Finset ItemType)) =>
          sq_nonneg (I.valuation I.smallestGroup z))).mp hu
    exact ⟨z, by nlinarith [hvalue I.smallestGroup z]⟩
  have hnormalized_le (i : Group) (z : ItemType) :
      copy_weighted_normalized_value I i z ≤
        maximum_copy_normalized_item_value I := by
    simpa [maximum_copy_normalized_item_value] using
      (Finset.le_sup'
        (s := (Finset.univ.product Finset.univ : Finset (Group × ItemType)))
        (f := fun p => copy_weighted_normalized_value I p.1 p.2)
        (by simp : (i, z) ∈
          (Finset.univ.product Finset.univ : Finset (Group × ItemType))))
  have hmax : 0 < maximum_copy_normalized_item_value I := by
    obtain ⟨z, hz⟩ := hsome_value_pos
    have hz' : 0 < copy_weighted_normalized_value I I.smallestGroup z := by
      rw [copy_weighted_normalized_value]
      exact div_pos hz (hcopy_norm I.smallestGroup)
    exact lt_of_lt_of_le hz' (hnormalized_le I.smallestGroup z)
  have hnormalized_sq_sum (i : Group) :
      ∑ z, (I.copies z : ℝ) *
          (copy_weighted_normalized_value I i z) ^ 2 = 1 := by
    have hsqrt_sq :
        (copy_weighted_valuation_norm I i) ^ 2 =
          ∑ z, (I.copies z : ℝ) * (I.valuation i z) ^ 2 := by
      rw [copy_weighted_valuation_norm, Real.sq_sqrt]
      exact Finset.sum_nonneg fun z _ =>
        mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    calc
      (∑ z, (I.copies z : ℝ) *
          (copy_weighted_normalized_value I i z) ^ 2) =
          (∑ z, (I.copies z : ℝ) * (I.valuation i z) ^ 2) /
            (copy_weighted_valuation_norm I i) ^ 2 := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl fun z _ => by
          rw [copy_weighted_normalized_value, div_pow, div_eq_mul_inv]
          ring
      _ = 1 := by
        rw [← hsqrt_sq]
        field_simp [ne_of_gt (hcopy_norm i)]
  let average : ItemType → ℝ := fun z =>
    (∑ i, (I.groupSize i : ℝ) *
      copy_weighted_normalized_value I i z) / (number_of_agents I : ℝ)
  have haverage_nonneg (z : ItemType) : 0 ≤ average z := by
    dsimp [average]
    exact div_nonneg
      (Finset.sum_nonneg fun i _ =>
        mul_nonneg (Nat.cast_nonneg _) (hnormalized_nonneg i z))
      (le_of_lt hn)
  have haverage_le (z : ItemType) :
      average z ≤ maximum_copy_normalized_item_value I := by
    rw [show average z =
      (∑ i, (I.groupSize i : ℝ) *
        copy_weighted_normalized_value I i z) /
          (number_of_agents I : ℝ) by rfl]
    rw [div_le_iff₀ hn]
    calc
      (∑ i, (I.groupSize i : ℝ) *
          copy_weighted_normalized_value I i z) ≤
          ∑ i, (I.groupSize i : ℝ) *
            maximum_copy_normalized_item_value I := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hnormalized_le i z) (Nat.cast_nonneg _)
      _ = maximum_copy_normalized_item_value I *
          (number_of_agents I : ℝ) := by
        rw [← Finset.sum_mul]
        rw [show (∑ i, (I.groupSize i : ℝ)) =
          (number_of_agents I : ℝ) by simp [number_of_agents]]
        exact mul_comm _ _
  let X : fractional_allocation I := fun i j =>
    (1 / (number_of_agents I : ℝ)) *
      (1 + (copy_weighted_normalized_value I i j.1 - average j.1) /
        maximum_copy_normalized_item_value I)
  have hX_nonneg (i : Group) (j : copied_item I) : 0 ≤ X i j := by
    have hinside :
        0 ≤ 1 +
          (copy_weighted_normalized_value I i j.1 - average j.1) /
            maximum_copy_normalized_item_value I := by
      have hdiv :
          -1 ≤
            (copy_weighted_normalized_value I i j.1 - average j.1) /
              maximum_copy_normalized_item_value I := by
        rw [le_div_iff₀ hmax]
        nlinarith [hnormalized_nonneg i j.1, haverage_le j.1]
      linarith
    dsimp [X]
    exact mul_nonneg (by positivity) hinside
  have hX_complete (j : copied_item I) :
      ∑ i, (I.groupSize i : ℝ) * X i j = 1 := by
    have hsum_sizes :
        ∑ i, (I.groupSize i : ℝ) = (number_of_agents I : ℝ) := by
      simp [number_of_agents]
    have hperturb :
        ∑ i, (I.groupSize i : ℝ) *
          (copy_weighted_normalized_value I i j.1 - average j.1) = 0 := by
      calc
        (∑ i, (I.groupSize i : ℝ) *
          (copy_weighted_normalized_value I i j.1 - average j.1)) =
            (∑ i, (I.groupSize i : ℝ) *
              copy_weighted_normalized_value I i j.1) -
            (∑ i, (I.groupSize i : ℝ) * average j.1) := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by
          rw [← Finset.sum_mul, hsum_sizes]
          dsimp [average]
          field_simp [ne_of_gt hn]
          ring
    calc
      (∑ i, (I.groupSize i : ℝ) * X i j) =
          ∑ i, ((1 / (number_of_agents I : ℝ)) *
              (I.groupSize i : ℝ) +
            (1 / ((number_of_agents I : ℝ) *
                maximum_copy_normalized_item_value I)) *
              ((I.groupSize i : ℝ) *
                (copy_weighted_normalized_value I i j.1 - average j.1))) := by
        exact Finset.sum_congr rfl fun i _ => by
          dsimp [X]
          ring
      _ = 1 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hsum_sizes, hperturb]
        field_simp [ne_of_gt hn]
        ring
  refine ⟨X, hX_nonneg, hX_complete, ?_⟩
  intro i i' hii'
  have hminimum_le :
      minimum_copy_weighted_separation_squared I ≤
        copy_weighted_separation_squared I i i' := by
    let pairs : Finset (Group × Group) :=
      (Finset.univ.product Finset.univ).filter (fun p => p.1 ≠ p.2)
    have hpairs : pairs.Nonempty :=
      ⟨(i, i'), by simp [pairs, hii']⟩
    rw [minimum_copy_weighted_separation_squared]
    rw [dif_pos hpairs]
    exact Finset.inf'_le _
      (show (i, i') ∈
        (Finset.univ.product Finset.univ).filter
          (fun p : Group × Group => p.1 ≠ p.2) from by simp [hii'])
  have hdistance :
      copy_weighted_separation_squared I i i' =
        2 * ∑ z, (I.copies z : ℝ) *
          copy_weighted_normalized_value I i z *
          (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z) := by
    rw [copy_weighted_separation_squared]
    have hi := hnormalized_sq_sum i
    have hi' := hnormalized_sq_sum i'
    have hdist_nonneg :
        0 ≤ ∑ z, (I.copies z : ℝ) *
          (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z) ^ 2 :=
      Finset.sum_nonneg fun z _ =>
        mul_nonneg (Nat.cast_nonneg (I.copies z))
          (sq_nonneg (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z))
    have hsq :
        (∑ z, (I.copies z : ℝ) *
          (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z) ^ 2) =
          (∑ z, (I.copies z : ℝ) *
            (copy_weighted_normalized_value I i z) ^ 2) +
          (∑ z, (I.copies z : ℝ) *
            (copy_weighted_normalized_value I i' z) ^ 2) -
          2 * ∑ z, (I.copies z : ℝ) *
            copy_weighted_normalized_value I i z *
              copy_weighted_normalized_value I i' z := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    have hprod :
        2 * (∑ z, (I.copies z : ℝ) *
          (copy_weighted_normalized_value I i z) ^ 2) -
          2 * ∑ z, (I.copies z : ℝ) *
            copy_weighted_normalized_value I i z *
              copy_weighted_normalized_value I i' z =
        2 * ∑ z, (I.copies z : ℝ) *
          copy_weighted_normalized_value I i z *
            (copy_weighted_normalized_value I i z -
              copy_weighted_normalized_value I i' z) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    calc
      (∑ z, (I.copies z : ℝ) *
        (copy_weighted_normalized_value I i z -
          copy_weighted_normalized_value I i' z) ^ 2) =
          (∑ z, (I.copies z : ℝ) *
            (copy_weighted_normalized_value I i z) ^ 2) +
          (∑ z, (I.copies z : ℝ) *
            (copy_weighted_normalized_value I i' z) ^ 2) -
          2 * ∑ z, (I.copies z : ℝ) *
            copy_weighted_normalized_value I i z *
              copy_weighted_normalized_value I i' z := hsq
      _ = 2 * (∑ z, (I.copies z : ℝ) *
            (copy_weighted_normalized_value I i z) ^ 2) -
          2 * ∑ z, (I.copies z : ℝ) *
            copy_weighted_normalized_value I i z *
              copy_weighted_normalized_value I i' z := by
        rw [hi, hi']
        ring
      _ = 2 * ∑ z, (I.copies z : ℝ) *
          copy_weighted_normalized_value I i z *
            (copy_weighted_normalized_value I i z -
              copy_weighted_normalized_value I i' z) := hprod
  have hgap :
      fractional_bundle_value I X i i -
          fractional_bundle_value I X i i' =
        copy_weighted_valuation_norm I i *
          copy_weighted_separation_squared I i i' /
            (2 * (number_of_agents I : ℝ) *
              maximum_copy_normalized_item_value I) := by
    have hX_sub (j : copied_item I) :
        X i j - X i' j =
          (copy_weighted_normalized_value I i j.1 -
            copy_weighted_normalized_value I i' j.1) /
              ((number_of_agents I : ℝ) *
                maximum_copy_normalized_item_value I) := by
      dsimp [X]
      ring
    have hvaluation_eq (z : ItemType) :
        I.valuation i z =
          copy_weighted_valuation_norm I i *
            copy_weighted_normalized_value I i z := by
      rw [copy_weighted_normalized_value]
      field_simp [ne_of_gt (hcopy_norm i)]
    rw [fractional_bundle_value, fractional_bundle_value,
      ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, hX_sub]
    change
      (∑ j : (Σ z : ItemType, Fin (I.copies z)),
        I.valuation i j.1 *
          ((copy_weighted_normalized_value I i j.1 -
            copy_weighted_normalized_value I i' j.1) /
              ((number_of_agents I : ℝ) *
                maximum_copy_normalized_item_value I))) =
      copy_weighted_valuation_norm I i *
        copy_weighted_separation_squared I i i' /
          (2 * (number_of_agents I : ℝ) *
            maximum_copy_normalized_item_value I)
    rw [Fintype.sum_sigma]
    simp
    calc
      (∑ z, (I.copies z : ℝ) *
          (I.valuation i z *
            ((copy_weighted_normalized_value I i z -
              copy_weighted_normalized_value I i' z) /
                ((number_of_agents I : ℝ) *
                  maximum_copy_normalized_item_value I)))) =
          (copy_weighted_valuation_norm I i /
            ((number_of_agents I : ℝ) *
              maximum_copy_normalized_item_value I)) *
            ∑ z, (I.copies z : ℝ) *
              copy_weighted_normalized_value I i z *
                (copy_weighted_normalized_value I i z -
                  copy_weighted_normalized_value I i' z) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by
          rw [hvaluation_eq]
          ring
      _ = copy_weighted_valuation_norm I i *
          copy_weighted_separation_squared I i i' /
            (2 * (number_of_agents I : ℝ) *
              maximum_copy_normalized_item_value I) := by
        rw [hdistance]
        ring
  rw [hgap]
  have hden : 0 <
      2 * (number_of_agents I : ℝ) *
        maximum_copy_normalized_item_value I := by positivity
  have hquotient :=
    (div_le_div_iff_of_pos_right hden).2 hminimum_le
  simp only [Prod.snd]
  calc
    copy_weighted_valuation_norm I i *
        (minimum_copy_weighted_separation_squared I /
          (2 * (number_of_agents I : ℝ) *
            maximum_copy_normalized_item_value I)) ≤
      copy_weighted_valuation_norm I i *
        (copy_weighted_separation_squared I i i' /
          (2 * (number_of_agents I : ℝ) *
            maximum_copy_normalized_item_value I)) :=
      mul_le_mul_of_nonneg_left hquotient (le_of_lt (hcopy_norm i))
    _ = copy_weighted_valuation_norm I i *
        copy_weighted_separation_squared I i i' /
          (2 * (number_of_agents I : ℝ) *
            maximum_copy_normalized_item_value I) := by ring

@[blueprint "lem:finite-envy-gap-program-sparse-optimum"
  (statement := /-- Let $I$ be an admissible finite goods profile with strictly positive copy counts, and suppose that $(X_0,\alpha_0)$ is feasible for the max--min envy-gap program. Then the program has an optimal feasible pair $(X^*,\alpha^*)$ with $\alpha_0\le\alpha^*$ and at most $d(d-1)$ shared copied items. -/)
  (proof := /-- Restrict the feasible set to gap coordinates at least $\alpha_0$. Completeness and positivity of the group sizes bound every allocation coordinate, while any fixed ordered pair of distinct groups bounds the gap coordinate from above. The restricted feasible set is therefore nonempty and compact, so the gap coordinate attains a maximum. Among its maximizers choose one with minimum positive support.

If more than $d(d-1)$ copied items are shared, choose two positive group coordinates on each such item. The corresponding weighted transfer directions preserve completeness. Since there are only $d(d-1)$ ordered envy-gap functionals, finite-dimensional linear dependence supplies a nonzero combination of these directions that preserves every gap. Moving maximally in a suitable sign of this direction keeps all coordinates nonnegative and makes one positive coordinate vanish. This produces another maximizer with smaller positive support, a contradiction. -/)
  (title := /-- Sparse optimum for the finite envy-gap program -/)
  (latexEnv := "lemma")]
lemma finite_envy_gap_program_sparse_optimum {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (X₀ : fractional_allocation I) (α₀ : ℝ)
    (hfeasible : (X₀, α₀) ∈ max_min_envy_gap_feasible_set I) :
    ∃ X : fractional_allocation I, ∃ α : ℝ,
      (X, α) ∈ max_min_envy_gap_feasible_set I ∧
      (∀ Y : fractional_allocation I, ∀ β : ℝ,
        (Y, β) ∈ max_min_envy_gap_feasible_set I → β ≤ α) ∧
      α₀ ≤ α ∧
      shared_copied_items I X ≤
        number_of_groups I * (number_of_groups I - 1) := by
  classical
  letI : TopologicalSpace (fractional_allocation I) :=
    inferInstanceAs
      (TopologicalSpace (Group → copied_item I → ℝ))
  rcases hprofile with
    ⟨hsize, hsmallest, hlargest, hvalue, hunitnorm, hgroups, hunitsep⟩
  have hsize_real (i : Group) : 0 < (I.groupSize i : ℝ) := by
    exact_mod_cast hsize i
  have hweighted_sum_pos (i : Group) :
      0 < ∑ z, (I.copies z : ℝ) * (I.valuation i z) ^ 2 := by
    have hu : 0 < ∑ z, (I.valuation i z) ^ 2 :=
      Real.sqrt_pos.mp (hunitnorm i)
    refine lt_of_lt_of_le hu (Finset.sum_le_sum fun z _ => ?_)
    have hc : (1 : ℝ) ≤ I.copies z := by
      exact_mod_cast hpositive z
    nlinarith [sq_nonneg (I.valuation i z)]
  have hcopy_norm (i : Group) : 0 < copy_weighted_valuation_norm I i := by
    rw [copy_weighted_valuation_norm]
    exact Real.sqrt_pos.mpr (hweighted_sum_pos i)
  have hx_upper {X : fractional_allocation I} {α : ℝ}
      (hXα : (X, α) ∈ max_min_envy_gap_feasible_set I)
      (i : Group) (j : copied_item I) :
      X i j ≤ 1 / (I.groupSize i : ℝ) := by
    rcases hXα with ⟨hXnonneg, hXcomplete, hXgap⟩
    have hterm :
        (I.groupSize i : ℝ) * X i j ≤
          ∑ a, (I.groupSize a : ℝ) * X a j := by
      exact Finset.single_le_sum
        (fun a _ => mul_nonneg (Nat.cast_nonneg _) (hXnonneg a j))
        (Finset.mem_univ i)
    rw [hXcomplete j] at hterm
    rw [le_div_iff₀ (hsize_real i)]
    simpa [mul_comm] using hterm
  obtain ⟨i₀, i₁, hi₀i₁⟩ := hgroups
  let M : ℝ :=
    (∑ j : copied_item I,
      I.valuation i₀ j.1 * (1 / (I.groupSize i₀ : ℝ))) /
        copy_weighted_valuation_norm I i₀
  have halpha_upper {X : fractional_allocation I} {α : ℝ}
      (hXα : (X, α) ∈ max_min_envy_gap_feasible_set I) : α ≤ M := by
    rcases hXα with ⟨hXnonneg, hXcomplete, hXgap⟩
    have hother_nonneg : 0 ≤ fractional_bundle_value I X i₀ i₁ := by
      rw [fractional_bundle_value]
      exact Finset.sum_nonneg fun j _ =>
        mul_nonneg (hvalue i₀ j.1) (hXnonneg i₁ j)
    have hown_upper :
        fractional_bundle_value I X i₀ i₀ ≤
          ∑ j : copied_item I,
            I.valuation i₀ j.1 * (1 / (I.groupSize i₀ : ℝ)) := by
      rw [fractional_bundle_value]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left
          (hx_upper ⟨hXnonneg, hXcomplete, hXgap⟩ i₀ j)
          (hvalue i₀ j.1)
    have hscaled :
        copy_weighted_valuation_norm I i₀ * α ≤
          ∑ j : copied_item I,
            I.valuation i₀ j.1 * (1 / (I.groupSize i₀ : ℝ)) := by
      exact le_trans (hXgap i₀ i₁ hi₀i₁)
        (le_trans (sub_le_self _ hother_nonneg) hown_upper)
    dsimp [M]
    exact (le_div_iff₀ (hcopy_norm i₀)).2 (by
      simpa [mul_comm] using hscaled)
  let S : Set (fractional_allocation I × ℝ) :=
    {p | p ∈ max_min_envy_gap_feasible_set I ∧ α₀ ≤ p.2}
  have hcoord_continuous (i : Group) (j : copied_item I) :
      Continuous (fun p : fractional_allocation I × ℝ => p.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  have hbundle_continuous (i i' : Group) :
      Continuous (fun p : fractional_allocation I × ℝ =>
        fractional_bundle_value I p.1 i i') := by
    rw [show (fun p : fractional_allocation I × ℝ =>
      fractional_bundle_value I p.1 i i') =
        (fun p => ∑ j, I.valuation i j.1 * p.1 i' j) by
          funext p
          rfl]
    exact continuous_finset_sum _ fun j _ =>
      continuous_const.mul (hcoord_continuous i' j)
  have hnonneg_closed :
      IsClosed {p : fractional_allocation I × ℝ |
        ∀ i j, 0 ≤ p.1 i j} := by
    have hclosed : IsClosed
        (⋂ i : Group, ⋂ j : copied_item I,
          {p : fractional_allocation I × ℝ | (0 : ℝ) ≤ p.1 i j}) :=
      isClosed_iInter fun i =>
        isClosed_iInter fun j =>
          isClosed_le (continuous_const :
            Continuous (fun _ : fractional_allocation I × ℝ => (0 : ℝ)))
            (hcoord_continuous i j)
    rw [show {p : fractional_allocation I × ℝ |
        ∀ i j, 0 ≤ p.1 i j} =
      (⋂ i : Group, ⋂ j : copied_item I,
        {p : fractional_allocation I × ℝ | (0 : ℝ) ≤ p.1 i j}) by
          ext p
          simp]
    exact hclosed
  have hcomplete_closed :
      IsClosed {p : fractional_allocation I × ℝ |
        ∀ j, ∑ i, (I.groupSize i : ℝ) * p.1 i j = 1} := by
    have hclosed : IsClosed
        (⋂ j : copied_item I,
          {p : fractional_allocation I × ℝ |
            ∑ i, (I.groupSize i : ℝ) * p.1 i j = 1}) :=
      isClosed_iInter fun j =>
        isClosed_eq
          (continuous_finset_sum _ fun i _ =>
            continuous_const.mul (hcoord_continuous i j))
          (continuous_const :
            Continuous (fun _ : fractional_allocation I × ℝ => (1 : ℝ)))
    rw [show {p : fractional_allocation I × ℝ |
        ∀ j, ∑ i, (I.groupSize i : ℝ) * p.1 i j = 1} =
      (⋂ j : copied_item I,
        {p : fractional_allocation I × ℝ |
          ∑ i, (I.groupSize i : ℝ) * p.1 i j = 1}) by
          ext p
          simp]
    exact hclosed
  have hgap_closed :
      IsClosed {p : fractional_allocation I × ℝ |
        ∀ i i', i ≠ i' →
          copy_weighted_valuation_norm I i * p.2 ≤
            fractional_bundle_value I p.1 i i -
              fractional_bundle_value I p.1 i i'} := by
    have hclosed : IsClosed
        (⋂ i : Group, ⋂ i' : Group,
          {p : fractional_allocation I × ℝ |
            i ≠ i' →
              copy_weighted_valuation_norm I i * p.2 ≤
                fractional_bundle_value I p.1 i i -
                  fractional_bundle_value I p.1 i i'}) :=
      isClosed_iInter fun i =>
        isClosed_iInter fun i' => by
        by_cases hii' : i = i'
        · subst i'
          simp
        · simpa [hii'] using
            (isClosed_le (continuous_const.mul continuous_snd)
              ((hbundle_continuous i i).sub (hbundle_continuous i i')))
    rw [show {p : fractional_allocation I × ℝ |
        ∀ i i', i ≠ i' →
          copy_weighted_valuation_norm I i * p.2 ≤
            fractional_bundle_value I p.1 i i -
              fractional_bundle_value I p.1 i i'} =
      (⋂ i : Group, ⋂ i' : Group,
        {p : fractional_allocation I × ℝ |
          i ≠ i' →
            copy_weighted_valuation_norm I i * p.2 ≤
              fractional_bundle_value I p.1 i i -
                fractional_bundle_value I p.1 i i'}) by
          ext p
          simp]
    exact hclosed
  have hS_closed : IsClosed S := by
    have halpha_closed :
        IsClosed {p : fractional_allocation I × ℝ | α₀ ≤ p.2} :=
      isClosed_le continuous_const continuous_snd
    have hfeasible_closed :
        IsClosed (max_min_envy_gap_feasible_set I) := by
      simpa [max_min_envy_gap_feasible_set, Set.setOf_and] using
        (hnonneg_closed.inter (hcomplete_closed.inter hgap_closed))
    simpa [S, Set.setOf_and] using hfeasible_closed.inter halpha_closed
  let XBox : Set (fractional_allocation I) :=
    {X | ∀ i j, X i j ∈ Set.Icc 0 (1 / (I.groupSize i : ℝ))}
  have hXBox_compact : IsCompact XBox := by
    dsimp [XBox]
    exact isCompact_pi_infinite fun i =>
      isCompact_pi_infinite fun j => isCompact_Icc
  let Box : Set (fractional_allocation I × ℝ) :=
    XBox ×ˢ Set.Icc α₀ M
  have hBox_compact : IsCompact Box := by
    exact hXBox_compact.prod isCompact_Icc
  have hS_subset_Box : S ⊆ Box := by
    intro p hp
    rcases hp with ⟨hpfeasible, hpalpha⟩
    refine ⟨?_, hpalpha, halpha_upper hpfeasible⟩
    intro i j
    exact ⟨hpfeasible.1 i j, hx_upper hpfeasible i j⟩
  have hS_compact : IsCompact S :=
    hBox_compact.of_isClosed_subset hS_closed hS_subset_Box
  have hS_nonempty : S.Nonempty := ⟨(X₀, α₀), hfeasible, le_rfl⟩
  obtain ⟨p, hpS, hpmax⟩ :=
    hS_compact.exists_isMaxOn hS_nonempty continuous_snd.continuousOn
  have hpoptimal :
      ∀ Y : fractional_allocation I, ∀ β : ℝ,
        (Y, β) ∈ max_min_envy_gap_feasible_set I → β ≤ p.2 := by
    intro Y β hYβ
    by_cases hα₀β : α₀ ≤ β
    · exact hpmax ⟨hYβ, hα₀β⟩
    · exact le_trans (le_of_not_ge hα₀β) hpS.2
  let support : fractional_allocation I → Finset (Group × copied_item I) :=
    fun X => Finset.univ.filter (fun q => 0 < X q.1 q.2)
  let P : ℕ → Prop := fun n =>
    ∃ X : fractional_allocation I,
      (X, p.2) ∈ max_min_envy_gap_feasible_set I ∧
      (support X).card = n
  have hP : ∃ n, P n :=
    ⟨(support p.1).card, p.1, hpS.1, rfl⟩
  obtain ⟨X, hXfeasible, hXsupport⟩ := Nat.find_spec hP
  have hsupport_minimal (Y : fractional_allocation I)
      (hYfeasible : (Y, p.2) ∈ max_min_envy_gap_feasible_set I) :
      (support X).card ≤ (support Y).card := by
    rw [hXsupport]
    exact Nat.find_min' hP ⟨Y, hYfeasible, rfl⟩
  refine ⟨X, p.2, hXfeasible, hpoptimal, hpS.2, ?_⟩
  let Shared :=
    {j : copied_item I //
      ∃ i i', i ≠ i' ∧ 0 < X i j ∧ 0 < X i' j}
  let Pairs := {q : Group × Group // q.1 ≠ q.2}
  let diagonalEquiv : Group ≃ {q : Group × Group // q.1 = q.2} :=
    { toFun := fun i => ⟨(i, i), rfl⟩
      invFun := fun q => q.1.1
      left_inv := fun _ => rfl
      right_inv := fun q => by
        apply Subtype.ext
        exact Prod.ext rfl q.property }
  have hcard_pairs :
      Fintype.card Pairs =
        number_of_groups I * (number_of_groups I - 1) := by
    have hcomplement : Fintype.card Pairs =
        Fintype.card (Group × Group) -
          Fintype.card {q : Group × Group // q.1 = q.2} := by
      simpa [Pairs] using
        (Fintype.card_subtype_compl
          (p := fun q : Group × Group => q.1 = q.2))
    have hdiagonal :
        Fintype.card {q : Group × Group // q.1 = q.2} =
          Fintype.card Group :=
      (Fintype.card_congr diagonalEquiv).symm
    rw [hcomplement, Fintype.card_prod, hdiagonal]
    simp only [number_of_groups]
    rw [Nat.mul_sub_left_distrib]
    simp
  change Nat.card Shared ≤
    number_of_groups I * (number_of_groups I - 1)
  rw [Nat.card_eq_fintype_card, ← hcard_pairs]
  by_contra hcard
  have hcard_lt : Fintype.card Pairs < Fintype.card Shared := by
    omega
  let left : Shared → Group := fun s => Classical.choose s.property
  let right : Shared → Group := fun s =>
    Classical.choose (Classical.choose_spec s.property)
  have hwitness (s : Shared) :
      left s ≠ right s ∧ 0 < X (left s) s.1 ∧
        0 < X (right s) s.1 :=
    Classical.choose_spec (Classical.choose_spec s.property)
  let direction : Shared → fractional_allocation I := fun s a j =>
    if j = s.1 then
      (if a = left s then 1 / (I.groupSize (left s) : ℝ) else 0) -
      (if a = right s then 1 / (I.groupSize (right s) : ℝ) else 0)
    else 0
  have hdirection_complete (s : Shared) (j : copied_item I) :
      ∑ a, (I.groupSize a : ℝ) * direction s a j = 0 := by
    by_cases hj : j = s.1
    · subst j
      dsimp [direction]
      simp only [↓reduceIte]
      calc
        (∑ a, (I.groupSize a : ℝ) *
          ((if a = left s then 1 / (I.groupSize (left s) : ℝ) else 0) -
            (if a = right s then 1 / (I.groupSize (right s) : ℝ) else 0))) =
            (∑ a, (I.groupSize a : ℝ) *
              (if a = left s then 1 / (I.groupSize (left s) : ℝ) else 0)) -
            (∑ a, (I.groupSize a : ℝ) *
              (if a = right s then 1 / (I.groupSize (right s) : ℝ) else 0)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun a _ => by ring
        _ = 0 := by
          simp
          field_simp [ne_of_gt (hsize_real (left s)),
            ne_of_gt (hsize_real (right s))]
          ring
    · simp [direction, hj]
  let effect : Shared → Pairs → ℝ := fun s q =>
    fractional_bundle_value I (direction s) q.1.1 q.1.1 -
      fractional_bundle_value I (direction s) q.1.1 q.1.2
  have heffect_dependent : ¬ LinearIndependent ℝ effect := by
    intro hindependent
    have hdim := hindependent.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hdim
    exact (not_le_of_gt hcard_lt) hdim
  obtain ⟨coefficient, hrelation, s₀, hs₀⟩ :=
    Fintype.not_linearIndependent_iff.mp heffect_dependent
  let D : fractional_allocation I := fun a j =>
    ∑ s, coefficient s * direction s a j
  have hD_complete (j : copied_item I) :
      ∑ a, (I.groupSize a : ℝ) * D a j = 0 := by
    dsimp [D]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun s _ => by
      rw [show (∑ a, (I.groupSize a : ℝ) *
          (coefficient s * direction s a j)) =
          coefficient s *
            ∑ a, (I.groupSize a : ℝ) * direction s a j by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring]
      rw [hdirection_complete, mul_zero]
  have hD_gap (q : Pairs) :
      fractional_bundle_value I D q.1.1 q.1.1 -
        fractional_bundle_value I D q.1.1 q.1.2 = 0 := by
    have hrel := congrFun hrelation q
    simp only [Pi.zero_apply, Finset.sum_apply, smul_eq_mul] at hrel
    rw [← hrel]
    dsimp [effect, D]
    simp only [fractional_bundle_value]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => rhs; rw [Finset.sum_comm]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      rw [show (∑ x, I.valuation q.1.1 x.1 *
          (coefficient s * direction s q.1.1 x)) =
          coefficient s *
            ∑ x, I.valuation q.1.1 x.1 * direction s q.1.1 x by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring]
      rw [show (∑ x, I.valuation q.1.1 x.1 *
          (coefficient s * direction s q.1.2 x)) =
          coefficient s *
            ∑ x, I.valuation q.1.1 x.1 * direction s q.1.2 x by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring]
      ring
  have hD_supported (a : Group) (j : copied_item I)
      (hDne : D a j ≠ 0) : 0 < X a j := by
    by_contra hnot
    have hdirzero (s : Shared) : direction s a j = 0 := by
      by_cases hj : j = s.1
      · subst j
        by_cases ha : a = left s
        · subst a
          exact False.elim (hnot (hwitness s).2.1)
        · by_cases ha' : a = right s
          · subst a
            exact False.elim (hnot (hwitness s).2.2)
          · simp [direction, ha, ha']
      · simp [direction, hj]
    apply hDne
    simp [D, hdirzero]
  have hD_at :
      D (left s₀) s₀.1 =
        coefficient s₀ * (1 / (I.groupSize (left s₀) : ℝ)) := by
    dsimp [D]
    rw [Fintype.sum_eq_single s₀]
    · simp [direction, (hwitness s₀).1]
    · intro s hs
      have hval : s.1 ≠ s₀.1 := by
        intro heq
        exact hs (Subtype.ext heq)
      simp [direction, hval, hval.symm]
  have hD_at_ne : D (left s₀) s₀.1 ≠ 0 := by
    rw [hD_at]
    exact mul_ne_zero hs₀
      (one_div_ne_zero (ne_of_gt (hsize_real (left s₀))))
  let scalar : ℝ := if D (left s₀) s₀.1 < 0 then 1 else -1
  let E : fractional_allocation I := fun a j => scalar * D a j
  have hscalar_ne : scalar ≠ 0 := by
    dsimp [scalar]
    split_ifs <;> norm_num
  have hE_negative : E (left s₀) s₀.1 < 0 := by
    dsimp [E, scalar]
    split_ifs with hneg
    · simpa using hneg
    · have hpos : 0 < D (left s₀) s₀.1 :=
        lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hD_at_ne)
      linarith
  have hE_complete (j : copied_item I) :
      ∑ a, (I.groupSize a : ℝ) * E a j = 0 := by
    dsimp [E]
    rw [show (∑ a, (I.groupSize a : ℝ) * (scalar * D a j)) =
        scalar * ∑ a, (I.groupSize a : ℝ) * D a j by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring]
    rw [hD_complete, mul_zero]
  have hE_gap (q : Pairs) :
      fractional_bundle_value I E q.1.1 q.1.1 -
        fractional_bundle_value I E q.1.1 q.1.2 = 0 := by
    have hbundle (a b : Group) :
        fractional_bundle_value I E a b =
          scalar * fractional_bundle_value I D a b := by
      rw [fractional_bundle_value, fractional_bundle_value]
      dsimp [E]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hbundle, hbundle, ← mul_sub, hD_gap, mul_zero]
  have hE_supported (a : Group) (j : copied_item I)
      (hEne : E a j ≠ 0) : 0 < X a j := by
    apply hD_supported a j
    intro hDzero
    apply hEne
    simp [E, hDzero]
  let Negative :=
    {q : Group × copied_item I // E q.1 q.2 < 0}
  let q₀ : Negative := ⟨(left s₀, s₀.1), hE_negative⟩
  have hnegative_nonempty :
      (Finset.univ : Finset Negative).Nonempty :=
    ⟨q₀, Finset.mem_univ _⟩
  let ratio : Negative → ℝ := fun q =>
    X q.1.1 q.1.2 / (-E q.1.1 q.1.2)
  have hratio_pos (q : Negative) : 0 < ratio q := by
    dsimp [ratio]
    exact div_pos
      (hE_supported q.1.1 q.1.2 (ne_of_lt q.2))
      (neg_pos.mpr q.2)
  let ε : ℝ :=
    (Finset.univ : Finset Negative).inf' hnegative_nonempty ratio
  have hε_pos : 0 < ε := by
    dsimp [ε]
    rw [Finset.lt_inf'_iff]
    intro q hq
    exact hratio_pos q
  have hε_le (q : Negative) :
      ε ≤ ratio q := by
    dsimp [ε]
    exact Finset.inf'_le _ (Finset.mem_univ q)
  obtain ⟨qmin, hqmin_mem, hqmin⟩ :=
    Finset.exists_mem_eq_inf' hnegative_nonempty ratio
  have hε_eq : ε = ratio qmin := by
    exact hqmin
  let Y : fractional_allocation I := fun a j =>
    X a j + ε * E a j
  have hY_nonneg (a : Group) (j : copied_item I) :
      0 ≤ Y a j := by
    by_cases hneg : E a j < 0
    · let q : Negative := ⟨(a, j), hneg⟩
      have hbound := hε_le q
      have hden : 0 < -E a j := neg_pos.mpr hneg
      have hmul := (le_div_iff₀ hden).mp hbound
      dsimp [q, ratio] at hmul
      dsimp [Y]
      nlinarith
    · have hE_nonneg : 0 ≤ E a j := le_of_not_gt hneg
      dsimp [Y]
      exact add_nonneg (hXfeasible.1 a j)
        (mul_nonneg (le_of_lt hε_pos) hE_nonneg)
  have hY_complete (j : copied_item I) :
      ∑ a, (I.groupSize a : ℝ) * Y a j = 1 := by
    dsimp [Y]
    rw [show (∑ a, (I.groupSize a : ℝ) *
        (X a j + ε * E a j)) =
        (∑ a, (I.groupSize a : ℝ) * X a j) +
          ε * ∑ a, (I.groupSize a : ℝ) * E a j by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring]
    rw [hXfeasible.2.1 j, hE_complete, mul_zero, add_zero]
  have hY_bundle (a b : Group) :
      fractional_bundle_value I Y a b =
        fractional_bundle_value I X a b +
          ε * fractional_bundle_value I E a b := by
    rw [fractional_bundle_value, fractional_bundle_value,
      fractional_bundle_value]
    dsimp [Y]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hY_gap (a b : Group) (hab : a ≠ b) :
      copy_weighted_valuation_norm I a * p.2 ≤
        fractional_bundle_value I Y a a -
          fractional_bundle_value I Y a b := by
    let q : Pairs := ⟨(a, b), hab⟩
    rw [hY_bundle, hY_bundle]
    have hzero := hE_gap q
    dsimp [q] at hzero
    nlinarith [hXfeasible.2.2 a b hab]
  have hY_feasible :
      (Y, p.2) ∈ max_min_envy_gap_feasible_set I :=
    ⟨hY_nonneg, hY_complete, hY_gap⟩
  have hsupport_subset : support Y ⊆ support X := by
    intro q hq
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    by_contra hnot
    have hXzero : X q.1 q.2 = 0 :=
      le_antisymm (le_of_not_gt hnot) (hXfeasible.1 q.1 q.2)
    have hEzero : E q.1 q.2 = 0 := by
      by_contra hne
      exact hnot (hE_supported q.1 q.2 hne)
    dsimp [Y] at hq
    rw [hXzero, hEzero] at hq
    linarith
  have hY_qmin_zero : Y qmin.1.1 qmin.1.2 = 0 := by
    have hden : -E qmin.1.1 qmin.1.2 ≠ 0 :=
      ne_of_gt (neg_pos.mpr qmin.2)
    have hEne : E qmin.1.1 qmin.1.2 ≠ 0 := ne_of_lt qmin.2
    dsimp [Y]
    rw [hε_eq]
    dsimp [ratio]
    field_simp [hden, hEne]
    ring
  have hqmin_support_X : qmin.1 ∈ support X := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hE_supported qmin.1.1 qmin.1.2 (ne_of_lt qmin.2)
  have hqmin_not_support_Y : qmin.1 ∉ support Y := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
      hY_qmin_zero, lt_self_iff_false, not_false_eq_true]
  have hsupport_strict : support Y ⊂ support X :=
    (Finset.ssubset_iff_of_subset hsupport_subset).2
      ⟨qmin.1, hqmin_support_X, hqmin_not_support_Y⟩
  have hsmaller := Finset.card_lt_card hsupport_strict
  have hminimal := hsupport_minimal Y hY_feasible
  omega

@[blueprint "lem:sparse-optimal-fractional-allocation"
  (statement := /-- Let $I$ be an admissible finite goods profile with positive copy counts. The max--min program of \cref{def:max-min-envy-gap-feasible-set} has an optimal solution $(X^*,\alpha^*)$ satisfying
  \[
    \alpha^*\ge
    \frac{\delta(\mathbf k)^2}
      {2n\widetilde v_{\max}(\mathbf k)}
    \quad\text{and}\quad
    |\operatorname{Shared}(X^*)|\le d(d-1).
  \]
  Here optimality means that every feasible $(Y,\beta)$ satisfies $\beta\le\alpha^*$. -/)
  (proof := /-- By \cref{lem:relative-norm-fractional-allocation-feasible}, the relative-norm construction gives a feasible pair whose gap coordinate is
  $\delta(\mathbf k)^2/(2n\widetilde v_{\max}(\mathbf k))$.
  Apply \cref{lem:finite-envy-gap-program-sparse-optimum} to this pair. The resulting feasible pair is globally optimal, its gap coordinate is no smaller than that of the relative-norm pair, and its number of shared copied items is at most $d(d-1)$, which are precisely the three required conclusions. -/)
  (title := /-- Sparse optimal solution of the envy-gap program -/)
  (latexEnv := "lemma")]
lemma sparse_optimal_fractional_allocation {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z) :
    ∃ X : fractional_allocation I, ∃ α : ℝ,
      (X, α) ∈ max_min_envy_gap_feasible_set I ∧
      (∀ Y : fractional_allocation I, ∀ β : ℝ,
        (Y, β) ∈ max_min_envy_gap_feasible_set I → β ≤ α) ∧
      minimum_copy_weighted_separation_squared I /
          (2 * (number_of_agents I : ℝ) *
            maximum_copy_normalized_item_value I) ≤ α ∧
      shared_copied_items I X ≤
        number_of_groups I * (number_of_groups I - 1) := by
  obtain ⟨X₀, hX₀⟩ :=
    relative_norm_fractional_allocation_feasible I hprofile hpositive
  obtain ⟨X, α, hXα, hoptimal, hlower, hsparse⟩ :=
    finite_envy_gap_program_sparse_optimum I hprofile hpositive X₀
      (minimum_copy_weighted_separation_squared I /
        (2 * (number_of_agents I : ℝ) *
          maximum_copy_normalized_item_value I)) hX₀
  exact ⟨X, α, hXα, hoptimal, hlower, hsparse⟩

@[blueprint "lem:finite-brauer-representation"
  (statement := /-- Let $S$ be a finite nonempty family of positive natural
  numbers with greatest common divisor $1$, with distinguished minimum $m$
  and maximum $M$. Every natural number $n$ satisfying
  $(m-1)(M-1)\le n$ is a nonnegative integral combination of the members of
  $S$. -/)
  (proof := /-- Proceed by strong induction on the cardinality of $S$. For a
  singleton, the gcd hypothesis forces its unique value to equal $1$. Otherwise,
  remove an index different from the distinguished minimum, and let $d$ be the
  gcd of the remaining values. The removed value and $d$ are coprime. Apply the
  two-generator Frobenius theorem to these two numbers, reduce the coefficient
  of the removed value modulo $d$, and apply the induction hypothesis to the
  remaining values after division by $d$. The reduced coefficient is less than
  $d$, and the original minimum--maximum bound implies the bound required by
  the induction hypothesis. Rescaling and adjoining the removed coefficient
  gives the required representation. -/)
  (title := /-- Brauer representation for a finite coprime family -/)
  (latexEnv := "lemma")]
lemma finite_brauer_representation {ι : Type*} (S : Finset ι) (a : ι → ℕ)
    (lo hi : ι) (hlo : lo ∈ S) (hhi : hi ∈ S)
    (hpos : ∀ i ∈ S, 0 < a i) (hmin : ∀ i ∈ S, a lo ≤ a i)
    (hmax : ∀ i ∈ S, a i ≤ a hi) (hgcd : S.gcd a = 1) (n : ℕ)
    (hbound : (a lo - 1) * (a hi - 1) ≤ n) :
    ∃ c : ι → ℕ, ∑ i ∈ S, c i * a i = n := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S a lo hi n with
  | h N ih =>
    by_cases hs : S = {lo}
    · subst S
      simp only [Finset.gcd_singleton] at hgcd
      have ha : a lo = 1 := by simpa using hgcd
      refine ⟨fun i => if i = lo then n else 0, ?_⟩
      simp [ha]
    · have hx : ∃ x ∈ S, x ≠ lo := by
        by_contra! h
        exact hs (Finset.eq_singleton_iff_unique_mem.mpr ⟨hlo, h⟩)
      obtain ⟨x, hxS, hxlo⟩ := hx
      let T := S.erase x
      have hloT : lo ∈ T := by simp [T, hlo, hxlo.symm]
      have hTne : T.Nonempty := ⟨lo, hloT⟩
      obtain ⟨hiT, hhiT, hmaxT⟩ := Finset.exists_max_image T a hTne
      let d := T.gcd a
      have hdvdlo : d ∣ a lo := Finset.gcd_dvd hloT
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvdlo (hpos lo hlo)
      have hdle : d ≤ a lo := Nat.le_of_dvd (hpos lo hlo) hdvdlo
      have hpair : (a x).gcd d = 1 := by
        rw [← gcd_eq_nat_gcd]
        calc
          gcd (a x) d = (insert x T).gcd a := by simp [d]
          _ = S.gcd a := by
            change (insert x (S.erase x)).gcd a = S.gcd a
            rw [Finset.insert_erase hxS]
          _ = 1 := hgcd
      have hpairbound : (a x).pred * d.pred ≤ n := by
        have hxpred : (a x).pred ≤ (a hi).pred := Nat.pred_le_pred (hmax x hxS)
        have hdpred : d.pred ≤ (a lo).pred := Nat.pred_le_pred hdle
        exact (Nat.mul_le_mul hxpred hdpred).trans (by simpa [mul_comm] using hbound)
      obtain ⟨u, v, huv⟩ :=
        Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (a x) d n
          (by simp [hpair]) hpairbound
      let r := u % d
      let k := v + u / d * a x
      have hrlt : r < d := Nat.mod_lt u hdpos
      have hdecomp : r * a x + k * d = n := by
        calc
          r * a x + k * d = (u % d + d * (u / d)) * a x + v * d := by
            simp only [r, k]
            ring
          _ = u * a x + v * d := by rw [Nat.mod_add_div]
          _ = n := huv
      let b : ι → ℕ := fun i => a i / d
      have hbpos : ∀ i ∈ T, 0 < b i := by
        intro i hi
        have hdi : d ∣ a i := Finset.gcd_dvd hi
        exact Nat.div_pos (Nat.le_of_dvd (hpos i (Finset.mem_of_mem_erase hi)) hdi) hdpos
      have hbmin : ∀ i ∈ T, b lo ≤ b i := by
        intro i hi
        exact Nat.div_le_div_right (hmin i (Finset.mem_of_mem_erase hi))
      have hbmax : ∀ i ∈ T, b i ≤ b hiT := by
        intro i hi
        exact Nat.div_le_div_right (hmaxT i hi)
      have hbgcd : T.gcd b = 1 := by
        simpa [b, d] using
          (Finset.gcd_div_eq_one (s := T) (f := a) hloT (ne_of_gt (hpos lo hlo)))
      have hkbound : (b lo - 1) * (b hiT - 1) ≤ k := by
        have hdvdhiT : d ∣ a hiT := Finset.gcd_dvd hhiT
        have hlo_scaled : d * b lo = a lo := by
          simpa [b] using Nat.mul_div_cancel' hdvdlo
        have hhi_scaled : d * b hiT = a hiT := by
          simpa [b] using Nat.mul_div_cancel' hdvdhiT
        have hhiTle : a hiT ≤ a hi := hmax hiT (Finset.mem_of_mem_erase hhiT)
        have hrle : r ≤ d - 1 := by omega
        have hblo_pos := hbpos lo hloT
        have hbhi_pos := hbpos hiT hhiT
        let A := b lo
        let B := b hiT
        let H := a hi
        let P := (A - 1) * (B - 1)
        change P ≤ k
        by_contra hnle
        have hklt : k < P := Nat.lt_of_not_ge hnle
        have hBleH : B ≤ H := by
          dsimp [B, H]
          nlinarith
        have hrx : r * a x ≤ (d - 1) * H := by
          exact Nat.mul_le_mul hrle (by simpa [H] using hmax x hxS)
        have hkle : k ≤ P - 1 := by omega
        have hnupper : n ≤ (d - 1) * H + (P - 1) * d := by
          rw [← hdecomp]
          exact Nat.add_le_add hrx (Nat.mul_le_mul_right d hkle)
        have hApos : 0 < A := by simpa [A] using hblo_pos
        have hBpos : 0 < B := by simpa [B] using hbhi_pos
        have hPpos : 0 < P := by omega
        have hAeq : A = (A - 1) + 1 := by omega
        have hBeq : B = (B - 1) + 1 := by omega
        have hdeq : d = (d - 1) + 1 := by omega
        have hHeq : H = B + (H - B) := by omega
        have hPeq : P = (P - 1) + 1 := by omega
        have hlo_scaled' : d * A = a lo := by simpa [A] using hlo_scaled
        have hDA : a lo - 1 = d * (A - 1) + (d - 1) := by
          rw [← hlo_scaled']
          calc
            d * A - 1 = d * ((A - 1) + 1) - 1 :=
              congrArg (fun z => d * z - 1) hAeq
            _ = d * (A - 1) + (d - 1) := by rw [mul_add, mul_one]; omega
        have hHm : H - 1 = (B - 1) + (H - B) := by omega
        have hPQ : (A - 1) * (B - 1) = (P - 1) + 1 := by
          rw [← hPeq]
        have hsmall : d + (d - 1) * (B - 1) = (d - 1) * B + 1 := by
          calc
            d + (d - 1) * (B - 1) = ((d - 1) + 1) + (d - 1) * (B - 1) := by rw [← hdeq]
            _ = (d - 1) * ((B - 1) + 1) + 1 := by ring
            _ = (d - 1) * B + 1 := by rw [← hBeq]
        have hid :
            (a lo - 1) * (H - 1) =
              (d - 1) * H + (P - 1) * d + d * (A - 1) * (H - B) + 1 := by
          rw [hDA, hHm]
          calc
            (d * (A - 1) + (d - 1)) * ((B - 1) + (H - B)) =
                d * (A - 1) * (B - 1) + (d - 1) * (B - 1) +
                  d * (A - 1) * (H - B) + (d - 1) * (H - B) := by ring
            _ = d * ((A - 1) * (B - 1)) + (d - 1) * (B - 1) +
                  d * (A - 1) * (H - B) + (d - 1) * (H - B) := by ring
            _ = d * ((P - 1) + 1) + (d - 1) * (B - 1) +
                  d * (A - 1) * (H - B) + (d - 1) * (H - B) := by
                    rw [hPQ]
            _ = (P - 1) * d + d * (A - 1) * (H - B) +
                  (d - 1) * (H - B) + (d + (d - 1) * (B - 1)) := by ring
            _ = (P - 1) * d + d * (A - 1) * (H - B) +
                  (d - 1) * (H - B) + ((d - 1) * B + 1) := by rw [hsmall]
            _ = (d - 1) * (B + (H - B)) + (P - 1) * d +
                  d * (A - 1) * (H - B) + 1 := by ring
            _ = (d - 1) * H + (P - 1) * d + d * (A - 1) * (H - B) + 1 := by rw [← hHeq]
        have : (d - 1) * H + (P - 1) * d < (a lo - 1) * (H - 1) := by
          rw [hid]
          omega
        have hlower : (a lo - 1) * (H - 1) ≤ n := by simpa [H] using hbound
        omega
      have hcardT : T.card < N := by
        calc
          T.card = (S.erase x).card := rfl
          _ < S.card := Finset.card_erase_lt_of_mem hxS
          _ = N := hcard
      obtain ⟨c, hc⟩ :=
        ih T.card hcardT T b lo hiT hloT hhiT hbpos hbmin hbmax hbgcd k hkbound rfl
      have hscale : ∑ i ∈ T, c i * a i = k * d := by
        calc
          ∑ i ∈ T, c i * a i = (∑ i ∈ T, c i * b i) * d := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            simp only [b]
            rw [mul_assoc, Nat.div_mul_cancel (Finset.gcd_dvd hi)]
          _ = k * d := by rw [hc]
      refine ⟨fun i => if i = x then r else c i, ?_⟩
      rw [← Finset.insert_erase hxS, Finset.sum_insert (by simp : x ∉ S.erase x)]
      simp only [if_pos]
      have hsum :
          ∑ i ∈ T, (if i = x then r else c i) * a i = ∑ i ∈ T, c i * a i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.ne_of_mem_erase hi]
      rw [hsum, hscale, hdecomp]

@[blueprint "lem:frobenius-brauer-group-size-representation"
  (statement := /-- Let $I$ be a grouped goods instance over finite group and
  item-type spaces. Assume that every group has positive size, the distinguished
  smallest and largest groups bound all group sizes, every valuation is
  nonnegative, every unit-copy valuation vector has positive Euclidean norm,
  at least two distinct groups exist, and the unit-copy normalized valuation
  vectors of every two distinct groups have positive squared Euclidean distance.
  Let $g$ be the greatest common divisor of the group sizes, let $n_1$ and $n_d$
  be the distinguished smallest and largest group sizes, and set
  \[
    \theta=g(n_1/g-1)(n_d/g-1).
  \]
  For every $s\in\mathbb N$ such that $\theta\le s$ and $g\mid s$, there exists
  a function $c$ from the groups to $\mathbb N$ satisfying
  \[
    \sum_i c(i)n_i=s.
  \] -/)
  (proof := /-- Let $g$ be the gcd from \cref{def:group-size-gcd}. It is positive
  because it divides the positive distinguished minimum group size. Divide every
  group size and $s$ by $g$. The reduced sizes are positive, retain the same
  distinguished minimum and maximum, and have gcd $1$. The hypothesis from
  \cref{def:frobenius-threshold}, divided by the positive integer $g$, gives
  \[
    (n_1/g-1)(n_d/g-1)\le s/g.
  \]
  Apply \cref{lem:finite-brauer-representation} to obtain coefficients whose
  combination of the reduced sizes is $s/g$. Since $g$ divides every original
  group size and divides $s$, multiplying this equality by $g$ gives
  $\sum_i c_i n_i=s$. -/)
  (title := /-- Frobenius--Brauer representation by group sizes -/)
  (latexEnv := "lemma")]
lemma frobenius_brauer_group_size_representation {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I) (s : ℕ)
    (hthreshold : frobenius_threshold I ≤ s)
    (hdiv : group_size_gcd I ∣ s) :
    ∃ c : Group → ℕ, ∑ i, c i * I.groupSize i = s := by
  classical
  rcases hprofile with
    ⟨hpos, hmin, hmax, hvalue, hnorm, hpairs, hseparation⟩
  let g := group_size_gcd I
  let a : Group → ℕ := fun i => I.groupSize i / g
  let t := s / g
  have hgdvd : ∀ i, g ∣ I.groupSize i := by
    intro i
    exact Finset.gcd_dvd (Finset.mem_univ i)
  have hgpos : 0 < g :=
    Nat.pos_of_dvd_of_pos (hgdvd I.smallestGroup) (hpos I.smallestGroup)
  have hapos : ∀ i ∈ (Finset.univ : Finset Group), 0 < a i := by
    intro i hi
    exact Nat.div_pos (Nat.le_of_dvd (hpos i) (hgdvd i)) hgpos
  have hamin : ∀ i ∈ (Finset.univ : Finset Group),
      a I.smallestGroup ≤ a i := by
    intro i hi
    exact Nat.div_le_div_right (hmin i)
  have hamax : ∀ i ∈ (Finset.univ : Finset Group),
      a i ≤ a I.largestGroup := by
    intro i hi
    exact Nat.div_le_div_right (hmax i)
  have hagcd : (Finset.univ : Finset Group).gcd a = 1 := by
    simpa [a, g, group_size_gcd] using
      (Finset.gcd_div_eq_one (s := (Finset.univ : Finset Group))
        (f := I.groupSize) (Finset.mem_univ I.smallestGroup)
        (ne_of_gt (hpos I.smallestGroup)))
  have htbound : (a I.smallestGroup - 1) * (a I.largestGroup - 1) ≤ t := by
    apply (Nat.le_div_iff_mul_le hgpos).2
    simpa [a, t, g, frobenius_threshold, mul_comm, mul_left_comm, mul_assoc] using
      hthreshold
  obtain ⟨c, hc⟩ := finite_brauer_representation
    (Finset.univ : Finset Group) a I.smallestGroup I.largestGroup
    (Finset.mem_univ _) (Finset.mem_univ _) hapos hamin hamax hagcd t htbound
  refine ⟨c, ?_⟩
  calc
    ∑ i, c i * I.groupSize i = (∑ i, c i * a i) * g := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_assoc, Nat.div_mul_cancel (hgdvd i)]
    _ = t * g := by rw [hc]
    _ = s := by exact Nat.div_mul_cancel hdiv

@[blueprint "lem:three-phase-prefix-threshold"
  (statement := /-- Let $w$ assign a natural-number weight at most $M$ to every
  entry of a finite list, where $M>0$.  If the total weight of the list is at
  least $T$, then some prefix has weight at least $T$ and strictly less than
  $T+M$. -/)
  (proof := /-- Induct on the list, allowing the threshold to vary.  For the
  empty list the total-weight hypothesis forces $T=0$, and the empty prefix
  works because $M>0$.  For a list beginning with $a$, use the singleton
  prefix if $T\le w(a)$.  Otherwise apply the induction hypothesis to the tail
  with residual threshold $T-w(a)$ and prepend $a$ to the resulting prefix.
  The weight bound on $a$ proves the strict overshoot estimate in the first
  case, and the induction hypothesis proves it in the second. -/)
  (title := /-- A bounded prefix crossing a weight threshold -/)
  (latexEnv := "lemma")]
lemma three_phase_prefix_threshold {ι : Type*} (w : ι → ℕ) (M : ℕ)
    (hM : 0 < M) (T : ℕ) (l : List ι) (hbound : ∀ x ∈ l, w x ≤ M)
    (htotal : T ≤ (l.map w).sum) :
    ∃ p s : List ι, l = p ++ s ∧ T ≤ (p.map w).sum ∧
      (p.map w).sum < T + M := by
  induction l generalizing T with
  | nil =>
      simp only [List.map_nil, List.sum_nil] at htotal
      have hT : T = 0 := by omega
      subst T
      exact ⟨[], [], rfl, le_rfl, by simpa using hM⟩
  | cons a l ih =>
      have ha : w a ≤ M := hbound a (by simp)
      have htail : ∀ x ∈ l, w x ≤ M := by
        intro x hx
        exact hbound x (by simp [hx])
      by_cases hT : T = 0
      · subst T
        exact ⟨[], a :: l, rfl, le_rfl, by simpa using hM⟩
      · by_cases hcross : T ≤ w a
        · exact ⟨[a], l, rfl, by simpa, by simp only [List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil]; omega⟩
        · have hresidual : T - w a ≤ (l.map w).sum := by
            simp only [List.map_cons, List.sum_cons] at htotal
            omega
          obtain ⟨p, s, hsplit, hlow, hupp⟩ :=
            ih (T - w a) htail hresidual
          refine ⟨a :: p, s, by simp [hsplit], ?_, ?_⟩
          · simp only [List.map_cons, List.sum_cons]
            omega
          · simp only [List.map_cons, List.sum_cons]
            omega

@[blueprint "lem:three-phase-weight-sum-by-value"
  (statement := /-- Let $w_i$ be natural-number weights on a finite index type.
  The sum of the weights of the entries of a finite list equals the sum, over
  all indices $i$, of $w_i$ times the multiplicity of $i$ in the list. -/)
  (proof := /-- Induct on the list.  The empty-list identity is immediate.  On
  adjoining an entry $i_0$, its weight is added on the left, while on the right
  exactly the count in the $i_0$-summand is
  increased by one; distributing the finite sum gives the same quantity. -/)
  (title := /-- Regrouping a weighted list sum by value -/)
  (latexEnv := "lemma")]
lemma three_phase_weight_sum_by_value {ι : Type*} [Fintype ι]
    [DecidableEq ι] (w : ι → ℕ) (l : List ι) :
    (l.map w).sum = ∑ i, l.count i * w i := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.count_cons]
      rw [ih]
      simp [Finset.sum_add_distrib, add_mul]
      ac_rfl

@[blueprint "lem:three-phase-integral-rounding"
  (statement := /-- Let $I$ be an admissible finite grouped-goods instance.  Write
  $d$ for its number of groups, $t$ for its number of item types, $n$ for its
  total number of agents, $n_d$ for its distinguished largest group size, $g$
  for the gcd of its group sizes, and $\theta$ for its Frobenius--Brauer
  threshold.  Assume that, for every item type $z$, the copy count $k_z$ is
  positive, satisfies $\theta\le k_z$, and is divisible by $g$.

  Let $X$ be a fractional allocation and let $\alpha\in\mathbb R$.  Suppose
  that $(X,\alpha)$ belongs to the max--min envy-gap feasible set and that $X$
  shares at most $d(d-1)$ individually indexed copies between distinct groups.
  Then there exists a complete integral allocation $A$ such that, for every
  ordered pair of distinct groups $i,i'$,
  \[
    \lVert v_i(\mathbf k)\rVert_2\alpha
      -2C\max_z v_{i,z}
      \le v_i(A_i)-v_i(A_{i'}),
  \]
  where $C=d(d-1)+t(\theta+n+n_d-d-1)$. -/)
  (proof := /-- Let $S$ be the set of shared individually indexed copies from
  \cref{def:shared-copied-items}.  The nonnegativity and completeness clauses
  of \cref{def:max-min-envy-gap-feasible-set} imply that every copy has a
  positive recipient.  If a copy is not in $S$, that recipient is unique; if
  it belongs to group $i$, completeness gives $n_iX_{i,j}=1$.  For every type
  $z$, let $B_{i,z}$ count the unshared copies uniquely owned by $i$, and put
  $q_{i,z}=\lfloor B_{i,z}/n_i\rfloor$.  Thus
  \[
    k_z=|S_z|+\sum_i(B_{i,z}\bmod n_i)+\sum_i n_iq_{i,z}.
  \]
  The first two terms form a base pool.  Since every $n_i>0$, the total of the
  remainders is at most $\sum_i(n_i-1)=n-d$.

  Form a list containing $q_{i,z}$ entries of weight $n_i$ for every group
  $i$.  Apply \cref{lem:three-phase-prefix-threshold} with residual threshold
  $\theta$ minus the base-pool size and with weight bound $n_d$.  Removing the
  resulting prefix leaves retained multiplicities $q'_{i,z}$ and a pool
  $R_z$ satisfying
  \[
    \theta\le R_z\le
    |S_z|+\sum_i(B_{i,z}\bmod n_i)+\theta+n_d-1.
  \]
  The regrouping identity in
  \cref{lem:three-phase-weight-sum-by-value} shows that the retained suffix has
  total weight $\sum_i n_iq'_{i,z}$.  Consequently
  $k_z=R_z+\sum_i n_iq'_{i,z}$.  Summing the displayed bound over $z$, using
  $|S|\le d(d-1)$, gives
  \[
    \sum_zR_z\le d(d-1)+t(\theta+n+n_d-d-1)=C.
  \]

  Every group size is divisible by $g$.  Since both $k_z$ and the retained
  total are divisible by $g$, so is $R_z$.  Hence
  \cref{lem:frobenius-brauer-group-size-representation} supplies natural
  numbers $c_{i,z}$ with $R_z=\sum_i c_{i,z}n_i$.  Define the common integral
  bundle by $A_{i,z}=q'_{i,z}+c_{i,z}$.  The preceding two identities prove
  completeness in the sense of \cref{def:complete-allocation}.

  For any group $g$ and type $z$, its fractional bundle consists of
  $B_{g,z}/n_g$ unshared owned copies together with its nonnegative fractions
  of copies in $S_z$.  Its loss on passing to the retained bundle is at most
  $R_z$ single-copy units.  Conversely, $q'_{g,z}\le B_{g,z}/n_g$, and the
  correction $c_{g,z}$ is at most $R_z$, so the integral bundle exceeds the
  fractional one by at most $R_z$ single-copy units.  By
  \cref{def:maximum-item-value} and the bound $\sum_zR_z\le C$, for every
  evaluating group $i$ and every group $g$,
  \[
    v_i(X_g)-C\max_z v_{i,z}\le v_i(A_g)
    \le v_i(X_g)+C\max_z v_{i,z}.
  \]
  Combining these two inequalities for $g=i$ and $g=i'$ with the feasible gap
  clause of \cref{def:max-min-envy-gap-feasible-set} loses at most
  $2C\max_zv_{i,z}$ and proves the asserted bound. -/)
  (title := /-- Three-phase rounding of a sparse fractional allocation -/)
  (latexEnv := "lemma")]
lemma three_phase_integral_rounding {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (htheta : ∀ z, frobenius_threshold I ≤ I.copies z)
    (hdiv : ∀ z, group_size_gcd I ∣ I.copies z)
    (X : fractional_allocation I) (α : ℝ)
    (hfeasible : (X, α) ∈ max_min_envy_gap_feasible_set I)
    (hshared : shared_copied_items I X ≤
      number_of_groups I * (number_of_groups I - 1)) :
    ∃ A : allocation Group ItemType, complete_allocation I A ∧
      ∀ i i', i ≠ i' →
        copy_weighted_valuation_norm I i * α -
            2 * (rounding_complexity I : ℝ) * maximum_item_value I i ≤
          bundle_value I A i i - bundle_value I A i i' := by
  classical
  have hsizepos : ∀ i, 0 < I.groupSize i := hprofile.1
  have hsizemax : ∀ i, I.groupSize i ≤ I.groupSize I.largestGroup :=
    hprofile.2.2.1
  have hval : ∀ i z, 0 ≤ I.valuation i z := hprofile.2.2.2.1
  rcases hfeasible with ⟨hXnonneg, hXcomplete, hXgap⟩
  let shared : Finset (copied_item I) :=
    Finset.univ.filter (fun j =>
      ∃ i i', i ≠ i' ∧ 0 < X i j ∧ 0 < X i' j)
  have hshared_card : shared.card = shared_copied_items I X := by
    rw [shared_copied_items, Nat.card_eq_fintype_card]
    simpa [shared] using
      (Fintype.card_subtype (fun j : copied_item I =>
        ∃ i i', i ≠ i' ∧ 0 < X i j ∧ 0 < X i' j)).symm
  have hex_owner (j : copied_item I) : ∃ i, 0 < X i j := by
    by_contra hnone
    push Not at hnone
    have hxzero : ∀ i, X i j = 0 := by
      intro i
      exact le_antisymm (hnone i) (hXnonneg i j)
    simpa [hxzero] using hXcomplete j
  let owner : copied_item I → Group := fun j => Classical.choose (hex_owner j)
  have howner_pos (j : copied_item I) : 0 < X (owner j) j :=
    Classical.choose_spec (hex_owner j)
  have howner_only {j : copied_item I} (hj : j ∉ shared) (i : Group)
      (hi : i ≠ owner j) : X i j = 0 := by
    apply le_antisymm
    · by_contra hnle
      have hipos : 0 < X i j := lt_of_not_ge hnle
      apply hj
      simp only [shared, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, owner j, hi, hipos, howner_pos j⟩
    · exact hXnonneg i j
  have howner_weight {j : copied_item I} (hj : j ∉ shared) :
      (I.groupSize (owner j) : ℝ) * X (owner j) j = 1 := by
    calc
      (I.groupSize (owner j) : ℝ) * X (owner j) j =
          ∑ i, (I.groupSize i : ℝ) * X i j := by
            symm
            apply Finset.sum_eq_single (owner j)
            · intro i hi hne
              rw [howner_only hj i hne]
              simp
            · simp
      _ = 1 := hXcomplete j
  let item (z : ItemType) (r : Fin (I.copies z)) : copied_item I := ⟨z, r⟩
  let sharedZ (z : ItemType) : Finset (Fin (I.copies z)) :=
    Finset.univ.filter (fun r => item z r ∈ shared)
  let unsharedZ (z : ItemType) : Finset (Fin (I.copies z)) :=
    Finset.univ.filter (fun r => item z r ∉ shared)
  let owned (i : Group) (z : ItemType) : Finset (Fin (I.copies z)) :=
    (unsharedZ z).filter (fun r => owner (item z r) = i)
  let B (i : Group) (z : ItemType) : ℕ := (owned i z).card
  let q (i : Group) (z : ItemType) : ℕ := B i z / I.groupSize i
  let basePool (z : ItemType) : ℕ :=
    (sharedZ z).card + ∑ i, B i z % I.groupSize i
  have howned_sum (z : ItemType) :
      ∑ i, B i z = (unsharedZ z).card := by
    simpa [B, owned] using
      (Finset.sum_card_fiberwise_eq_card_filter (unsharedZ z)
        (Finset.univ : Finset Group) (fun r => owner (item z r)))
  have hpartition (z : ItemType) :
      (sharedZ z).card + (unsharedZ z).card = I.copies z := by
    simpa [sharedZ, unsharedZ] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (I.copies z))))
        (fun r => item z r ∈ shared))
  have hBdecomp (z : ItemType) :
      (∑ i, B i z) =
        (∑ i, B i z % I.groupSize i) +
          ∑ i, I.groupSize i * q i z := by
    calc
      (∑ i, B i z) =
          ∑ i, (B i z % I.groupSize i + I.groupSize i * q i z) := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [q]
            have h := Nat.div_add_mod (B i z) (I.groupSize i)
            omega
      _ = (∑ i, B i z % I.groupSize i) +
          ∑ i, I.groupSize i * q i z := Finset.sum_add_distrib
  have hcopies_decomp (z : ItemType) :
      I.copies z = basePool z + ∑ i, I.groupSize i * q i z := by
    rw [← hpartition z, ← howned_sum z, hBdecomp z]
    simp only [basePool]
    omega
  let blocks (z : ItemType) : List Group :=
    (Finset.univ : Finset Group).toList.flatMap
      (fun i => List.replicate (q i z) i)
  have hblocks_sum (z : ItemType) :
      ((blocks z).map I.groupSize).sum =
        ∑ i, I.groupSize i * q i z := by
    simp [blocks, List.flatMap, Nat.mul_comm]
  have hprefix_exists (z : ItemType) :
      ∃ p s : List Group, blocks z = p ++ s ∧
        frobenius_threshold I - basePool z ≤
          (p.map I.groupSize).sum ∧
        (p.map I.groupSize).sum <
          frobenius_threshold I - basePool z + I.groupSize I.largestGroup := by
    refine three_phase_prefix_threshold
      (w := I.groupSize)
      (M := I.groupSize I.largestGroup) (hsizepos I.largestGroup)
      (T := frobenius_threshold I - basePool z) (l := blocks z) ?_ ?_
    · intro b hb
      exact hsizemax b
    · rw [hblocks_sum z]
      have hc := hcopies_decomp z
      have ht := htheta z
      omega
  choose removedBlocks retainedBlocks hsplit hprefix_low hprefix_high using hprefix_exists
  let pool (z : ItemType) : ℕ :=
    basePool z + ((removedBlocks z).map I.groupSize).sum
  let retained (i : Group) (z : ItemType) : ℕ :=
    (retainedBlocks z).count i
  have hsuffix_sum (z : ItemType) :
      ((retainedBlocks z).map I.groupSize).sum =
        ∑ i, retained i z * I.groupSize i := by
    simpa [retained] using
      (three_phase_weight_sum_by_value I.groupSize (retainedBlocks z))
  have hfinal_decomp (z : ItemType) :
      I.copies z = pool z + ∑ i, I.groupSize i * retained i z := by
    have hb := hblocks_sum z
    rw [hsplit z] at hb
    simp only [List.map_append, List.sum_append] at hb
    have hs := hsuffix_sum z
    simp only [pool]
    rw [hcopies_decomp z]
    rw [← hb, hs]
    simp_rw [Nat.mul_comm (retained _ z)]
    omega
  have hpool_threshold (z : ItemType) : frobenius_threshold I ≤ pool z := by
    have hlow := hprefix_low z
    simp only [pool]
    omega
  have hpool_bound (z : ItemType) :
      pool z ≤ basePool z + frobenius_threshold I +
        I.groupSize I.largestGroup - 1 := by
    have hupp := hprefix_high z
    simp only [pool]
    omega
  have hgsize (i : Group) : group_size_gcd I ∣ I.groupSize i := by
    exact Finset.gcd_dvd (Finset.mem_univ i)
  have hpool_div (z : ItemType) : group_size_gcd I ∣ pool z := by
    have hretained : group_size_gcd I ∣
        ∑ i, I.groupSize i * retained i z := by
      apply Finset.dvd_sum
      intro i hi
      exact dvd_mul_of_dvd_left (hgsize i) _
    have hsum : group_size_gcd I ∣
        (∑ i, I.groupSize i * retained i z) + pool z := by
      rw [Nat.add_comm, ← hfinal_decomp z]
      exact hdiv z
    exact (Nat.dvd_add_iff_right hretained).mpr hsum
  have hrepresentation (z : ItemType) :
      ∃ c : Group → ℕ, ∑ i, c i * I.groupSize i = pool z :=
    frobenius_brauer_group_size_representation I hprofile (pool z)
      (hpool_threshold z) (hpool_div z)
  choose correction hcorrection using hrepresentation
  let A : allocation Group ItemType := fun i z => retained i z + correction z i
  have hAcomplete : complete_allocation I A := by
    intro z
    simp only [A]
    simp_rw [Nat.mul_add]
    rw [Finset.sum_add_distrib]
    have hc := hcorrection z
    have hc' : (∑ i, I.groupSize i * correction z i) = pool z := by
      simpa [Nat.mul_comm] using hc
    rw [hc', Nat.add_comm, ← hfinal_decomp z]
  have hretained_le (i : Group) (z : ItemType) : retained i z ≤ q i z := by
    have hc := congrArg (List.count i) (hsplit z)
    simp only [List.count_append] at hc
    have hall : (blocks z).count i = q i z := by
      simp only [blocks, List.count_flatMap,
        Function.comp_apply]
      rw [Finset.sum_map_toList]
      calc
        (∑ j, List.count i (List.replicate (q j z) j)) =
            List.count i (List.replicate (q i z) i) := by
              apply Finset.sum_eq_single i
              · intro j hj hji
                simp [List.count_replicate, hji]
              · simp
        _ = q i z := by simp
    rw [hall] at hc
    simp only [retained]
    omega
  have hretained_copies_le (i : Group) (z : ItemType) :
      I.groupSize i * retained i z ≤ B i z := by
    have hq := hretained_le i z
    have hdivle := Nat.div_mul_le_self (B i z) (I.groupSize i)
    simp only [q] at hq
    nlinarith
  have hpool_count (z : ItemType) :
      pool z = (sharedZ z).card +
        ∑ i, (B i z - I.groupSize i * retained i z) := by
    have hsub :
        (∑ i, (B i z - I.groupSize i * retained i z)) =
          (∑ i, B i z) - ∑ i, I.groupSize i * retained i z := by
      apply Finset.sum_tsub_distrib
      intro i hi
      exact hretained_copies_le i z
    have hp := hpartition z
    rw [← howned_sum z] at hp
    have hf := hfinal_decomp z
    have hsumle : (∑ i, I.groupSize i * retained i z) ≤ ∑ i, B i z := by
      apply Finset.sum_le_sum
      intro i hi
      exact hretained_copies_le i z
    have heq : (sharedZ z).card + ∑ i, B i z =
        pool z + ∑ i, I.groupSize i * retained i z := hp.trans hf
    rw [hsub]
    omega
  have hsharedZ_sum : ∑ z, (sharedZ z).card = shared.card := by
    have hz (z : ItemType) :
        (sharedZ z).card =
          ∑ r : Fin (I.copies z), if item z r ∈ shared then 1 else 0 := by
      simp [sharedZ]
    simp_rw [hz]
    calc
      (∑ z, ∑ r : Fin (I.copies z),
          if (⟨z, r⟩ : copied_item I) ∈ shared then 1 else 0) =
          ∑ j : copied_item I, if j ∈ shared then 1 else 0 := by
            exact (Fintype.sum_sigma
              (fun j : copied_item I => if j ∈ shared then 1 else 0)).symm
      _ = shared.card := by simp
  have hgroups_le_agents : number_of_groups I ≤ number_of_agents I := by
    simp only [number_of_groups, number_of_agents]
    calc
      Fintype.card Group = ∑ _i : Group, 1 := by simp
      _ ≤ ∑ i, I.groupSize i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsizepos i
  have hremainder_bound (z : ItemType) :
      (∑ i, B i z % I.groupSize i) ≤
        number_of_agents I - number_of_groups I := by
    calc
      (∑ i, B i z % I.groupSize i) ≤
          ∑ i, (I.groupSize i - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            have hm := Nat.mod_lt (B i z) (hsizepos i)
            omega
      _ = number_of_agents I - number_of_groups I := by
            have hs : (∑ i, (I.groupSize i - 1)) =
                (∑ i, I.groupSize i) - ∑ _i : Group, 1 := by
              apply Finset.sum_tsub_distrib
              intro i hi
              exact hsizepos i
            rw [hs]
            simp [number_of_agents, number_of_groups]
  have hpool_simple_bound (z : ItemType) :
      pool z ≤ (sharedZ z).card +
        (frobenius_threshold I + number_of_agents I +
          I.groupSize I.largestGroup - number_of_groups I - 1) := by
    have hp := hpool_bound z
    have hr := hremainder_bound z
    simp only [basePool] at hp
    have hna := hgroups_le_agents
    omega
  have hpools_total : ∑ z, pool z ≤ rounding_complexity I := by
    let K := frobenius_threshold I + number_of_agents I +
      I.groupSize I.largestGroup - number_of_groups I - 1
    calc
      (∑ z, pool z) ≤ ∑ z, ((sharedZ z).card + K) := by
        apply Finset.sum_le_sum
        intro z hz
        exact hpool_simple_bound z
      _ = (∑ z, (sharedZ z).card) + number_of_types I * K := by
        rw [Finset.sum_add_distrib]
        simp [number_of_types]
      _ = shared.card + number_of_types I * K := by rw [hsharedZ_sum]
      _ ≤ number_of_groups I * (number_of_groups I - 1) +
          number_of_types I * K := by
        have hs : shared.card ≤ number_of_groups I * (number_of_groups I - 1) := by
          rw [hshared_card]
          exact hshared
        omega
      _ = rounding_complexity I := by rfl
  have hXle_one (i : Group) (j : copied_item I) : X i j ≤ 1 := by
    have hterm : (I.groupSize i : ℝ) * X i j ≤ 1 := by
      calc
        (I.groupSize i : ℝ) * X i j ≤
            ∑ i', (I.groupSize i' : ℝ) * X i' j := by
              have hs := Finset.single_le_sum
                (s := (Finset.univ : Finset Group))
                (f := fun i' => (I.groupSize i' : ℝ) * X i' j)
                (fun i' hi => mul_nonneg (Nat.cast_nonneg _) (hXnonneg i' j))
                (Finset.mem_univ i)
              simpa using hs
        _ = 1 := hXcomplete j
    have hs : (1 : ℝ) ≤ I.groupSize i := by
      exact_mod_cast hsizepos i
    have hx := hXnonneg i j
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) hx]
  let sharedPart (i : Group) (z : ItemType) : ℝ :=
    ∑ r ∈ sharedZ z, X i (item z r)
  let ownedPart (i : Group) (z : ItemType) : ℝ :=
    (B i z : ℝ) / (I.groupSize i : ℝ)
  have hunshared_sum (i : Group) (z : ItemType) :
      (∑ r ∈ unsharedZ z, X i (item z r)) = ownedPart i z := by
    have hrestrict : (∑ r ∈ owned i z, X i (item z r)) =
        ∑ r ∈ unsharedZ z, X i (item z r) := by
      apply Finset.sum_subset
      · intro r hr
        exact (Finset.mem_filter.mp hr).1
      · intro r hr hnot
        have hj : item z r ∉ shared := by
          simpa [unsharedZ] using hr
        have hne : i ≠ owner (item z r) := by
          intro heq
          apply hnot
          simp [owned, hr, heq]
        exact howner_only hj i hne
    rw [← hrestrict]
    calc
      (∑ r ∈ owned i z, X i (item z r)) =
          ∑ _r ∈ owned i z, (1 : ℝ) / I.groupSize i := by
            apply Finset.sum_congr rfl
            intro r hr
            have hmem := (Finset.mem_filter.mp hr)
            have hj : item z r ∉ shared := by
              simpa [unsharedZ] using hmem.1
            have ho : owner (item z r) = i := hmem.2
            have hw := howner_weight hj
            rw [ho] at hw
            apply (eq_div_iff (by exact_mod_cast (ne_of_gt (hsizepos i)))).2
            nlinarith
      _ = ownedPart i z := by
            simp [ownedPart, B, div_eq_mul_inv]
  have hcopy_sum (i : Group) (z : ItemType) :
      (∑ r : Fin (I.copies z), X i (item z r)) =
        ownedPart i z + sharedPart i z := by
    have hp := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Fin (I.copies z))))
      (fun r => item z r ∈ shared) (fun r => X i (item z r))
    have hs : (∑ r ∈ sharedZ z, X i (item z r)) = sharedPart i z := rfl
    have hu := hunshared_sum i z
    simp only [sharedZ, unsharedZ] at hs hu
    rw [← hp, hu, add_comm]
  have hfractional_decomp (eval g : Group) :
      fractional_bundle_value I X eval g =
        ∑ z, I.valuation eval z * (ownedPart g z + sharedPart g z) := by
    unfold fractional_bundle_value
    change (∑ j : copied_item I, I.valuation eval j.1 * X g j) = _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro z hz
    change (∑ y : Fin (I.copies z),
      I.valuation eval z * X g (item z y)) =
        I.valuation eval z * (ownedPart g z + sharedPart g z)
    rw [← Finset.mul_sum, hcopy_sum]
  have hsharedPart_nonneg (i : Group) (z : ItemType) :
      0 ≤ sharedPart i z := by
    apply Finset.sum_nonneg
    intro r hr
    exact hXnonneg i (item z r)
  have hsharedPart_le (i : Group) (z : ItemType) :
      sharedPart i z ≤ ((sharedZ z).card : ℝ) := by
    calc
      sharedPart i z ≤ ∑ _r ∈ sharedZ z, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hXle_one i (item z r)
      _ = ((sharedZ z).card : ℝ) := by simp
  have hretained_le_owned (i : Group) (z : ItemType) :
      (retained i z : ℝ) ≤ ownedPart i z := by
    have hn : (0 : ℝ) < I.groupSize i := by exact_mod_cast hsizepos i
    simp only [ownedPart]
    apply (le_div_iff₀ hn).2
    have hc : retained i z * I.groupSize i ≤ B i z := by
      simpa [Nat.mul_comm] using hretained_copies_le i z
    exact_mod_cast hc
  have howned_loss_le (i : Group) (z : ItemType) :
      ownedPart i z - retained i z ≤
        (B i z - I.groupSize i * retained i z : ℕ) := by
    have hn : (0 : ℝ) < I.groupSize i := by exact_mod_cast hsizepos i
    have hn1 : (1 : ℝ) ≤ I.groupSize i := by exact_mod_cast hsizepos i
    have hdiff : ((B i z - I.groupSize i * retained i z : ℕ) : ℝ) =
        (B i z : ℝ) - (I.groupSize i : ℝ) * retained i z := by
      exact_mod_cast Nat.cast_sub (hretained_copies_le i z)
    have hmul : ownedPart i z * I.groupSize i = (B i z : ℝ) := by
      simp [ownedPart, ne_of_gt hn]
    have hnon := sub_nonneg.mpr (hretained_le_owned i z)
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hnon]
  have hloss_per_type (i : Group) (z : ItemType) :
      ownedPart i z - retained i z + sharedPart i z ≤ (pool z : ℝ) := by
    have hsingle : B i z - I.groupSize i * retained i z ≤
        ∑ j, (B j z - I.groupSize j * retained j z) := by
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset Group))
        (f := fun j => B j z - I.groupSize j * retained j z)
        (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      simpa using hs
    have hc := hpool_count z
    have ho := howned_loss_le i z
    have hs := hsharedPart_le i z
    have hsingleR : ((B i z - I.groupSize i * retained i z : ℕ) : ℝ) ≤
        ((∑ j, (B j z - I.groupSize j * retained j z) : ℕ) : ℝ) := by
      exact_mod_cast hsingle
    have hcR : (pool z : ℝ) = (sharedZ z).card +
        ∑ j, (B j z - I.groupSize j * retained j z) := by
      exact_mod_cast hc
    linarith
  have hcorrection_le_pool (i : Group) (z : ItemType) :
      correction z i ≤ pool z := by
    have hterm : correction z i * I.groupSize i ≤ pool z := by
      rw [← hcorrection z]
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset Group))
        (f := fun j => correction z j * I.groupSize j)
        (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      simpa using hs
    nlinarith [hsizepos i]
  have hvmax (i : Group) (z : ItemType) :
      I.valuation i z ≤ maximum_item_value I i := by
    unfold maximum_item_value
    exact Finset.le_sup' (f := I.valuation i) (Finset.mem_univ z)
  have hmax_nonneg (i : Group) : 0 ≤ maximum_item_value I i :=
    le_trans (hval i I.someType) (hvmax i I.someType)
  have hloss_sum (eval g : Group) :
      (∑ z, I.valuation eval z *
        (ownedPart g z - retained g z + sharedPart g z)) ≤
          (rounding_complexity I : ℝ) * maximum_item_value I eval := by
    calc
      (∑ z, I.valuation eval z *
          (ownedPart g z - retained g z + sharedPart g z)) ≤
          ∑ z, maximum_item_value I eval * (pool z : ℝ) := by
            apply Finset.sum_le_sum
            intro z hz
            have he : 0 ≤ ownedPart g z - retained g z + sharedPart g z := by
              linarith [hretained_le_owned g z, hsharedPart_nonneg g z]
            calc
              I.valuation eval z *
                  (ownedPart g z - retained g z + sharedPart g z) ≤
                  maximum_item_value I eval *
                    (ownedPart g z - retained g z + sharedPart g z) :=
                mul_le_mul_of_nonneg_right (hvmax eval z) he
              _ ≤ maximum_item_value I eval * (pool z : ℝ) :=
                mul_le_mul_of_nonneg_left (hloss_per_type g z)
                  (hmax_nonneg eval)
      _ = maximum_item_value I eval * (∑ z, pool z : ℕ) := by
            rw [← Finset.mul_sum]
            simp
      _ ≤ maximum_item_value I eval * rounding_complexity I := by
            apply mul_le_mul_of_nonneg_left
            · exact_mod_cast hpools_total
            · exact hmax_nonneg eval
      _ = (rounding_complexity I : ℝ) * maximum_item_value I eval := by ring
  have hgain_sum (eval g : Group) :
      (∑ z, I.valuation eval z * (correction z g : ℝ)) ≤
        (rounding_complexity I : ℝ) * maximum_item_value I eval := by
    calc
      (∑ z, I.valuation eval z * (correction z g : ℝ)) ≤
          ∑ z, maximum_item_value I eval * (pool z : ℝ) := by
            apply Finset.sum_le_sum
            intro z hz
            have hc : (correction z g : ℝ) ≤ pool z := by
              exact_mod_cast hcorrection_le_pool g z
            calc
              I.valuation eval z * (correction z g : ℝ) ≤
                  maximum_item_value I eval * (correction z g : ℝ) :=
                mul_le_mul_of_nonneg_right (hvmax eval z) (Nat.cast_nonneg _)
              _ ≤ maximum_item_value I eval * (pool z : ℝ) :=
                mul_le_mul_of_nonneg_left hc (hmax_nonneg eval)
      _ = maximum_item_value I eval * (∑ z, pool z : ℕ) := by
            rw [← Finset.mul_sum]
            simp
      _ ≤ maximum_item_value I eval * rounding_complexity I := by
            apply mul_le_mul_of_nonneg_left
            · exact_mod_cast hpools_total
            · exact hmax_nonneg eval
      _ = (rounding_complexity I : ℝ) * maximum_item_value I eval := by ring
  have hlower_bundle (eval g : Group) :
      fractional_bundle_value I X eval g -
          (rounding_complexity I : ℝ) * maximum_item_value I eval ≤
        bundle_value I A eval g := by
    have hid :
        (∑ z, I.valuation eval z * (ownedPart g z + sharedPart g z)) =
          (∑ z, I.valuation eval z * (retained g z : ℝ)) +
            ∑ z, I.valuation eval z *
              (ownedPart g z - retained g z + sharedPart g z) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    have hcorr : 0 ≤ ∑ z, I.valuation eval z * (correction z g : ℝ) := by
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg (hval eval z) (Nat.cast_nonneg _)
    have hbundle : bundle_value I A eval g =
        (∑ z, I.valuation eval z * (retained g z : ℝ)) +
          ∑ z, I.valuation eval z * (correction z g : ℝ) := by
      simp [bundle_value, A, Nat.cast_add, mul_add,
        Finset.sum_add_distrib]
    rw [hbundle, hfractional_decomp, hid]
    linarith [hloss_sum eval g]
  have hupper_bundle (eval g : Group) :
      bundle_value I A eval g ≤ fractional_bundle_value I X eval g +
        (rounding_complexity I : ℝ) * maximum_item_value I eval := by
    have hret : (∑ z, I.valuation eval z * (retained g z : ℝ)) ≤
        ∑ z, I.valuation eval z * (ownedPart g z + sharedPart g z) := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (hval eval z)
      linarith [hretained_le_owned g z, hsharedPart_nonneg g z]
    have hbundle : bundle_value I A eval g =
        (∑ z, I.valuation eval z * (retained g z : ℝ)) +
          ∑ z, I.valuation eval z * (correction z g : ℝ) := by
      simp [bundle_value, A, Nat.cast_add, mul_add,
        Finset.sum_add_distrib]
    rw [hbundle, hfractional_decomp]
    linarith [hgain_sum eval g]
  refine ⟨A, hAcomplete, ?_⟩
  intro i i' hne
  have hg := hXgap i i' hne
  have hl := hlower_bundle i i
  have hu := hupper_bundle i i'
  linarith

@[blueprint "lem:rounded-allocation-gap-lower-bound"
  (statement := /-- Let $I$ be an admissible finite goods profile. Assume that every copy count is positive, at least $\theta$, and divisible by the gcd $g$ of the group sizes. Then there is a complete integral allocation $A$ such that, for every two distinct groups $i,i'$,
  \[
  v_i(A_i)-v_i(A_{i'})\ge
  \lVert v_i(\mathbf k)\rVert_2
  \frac{\delta(\mathbf k)^2}{2n\widetilde v_{\max}(\mathbf k)}
  -2C\max_zv_{i,z},
  \]
  where $C=d(d-1)+t(\theta+n+n_d-d-1)$ and $\delta(\mathbf k)^2$ is the minimum copy-weighted squared separation over distinct groups. -/)
  (proof := /-- Apply \cref{lem:sparse-optimal-fractional-allocation} to obtain a feasible pair $(X^*,\alpha^*)$ whose shared-item set has cardinality at most $d(d-1)$ and such that
  \[
    \frac{\delta(\mathbf k)^2}
      {2n\widetilde v_{\max}(\mathbf k)}
    \le\alpha^*.
  \]
  The hypotheses on the copy counts permit \cref{lem:three-phase-integral-rounding} to be applied to this pair. It supplies a complete integral allocation $A$ for which, whenever $i\ne i'$,
  \[
    \lVert v_i(\mathbf k)\rVert_2\alpha^*
      -2C\max_zv_{i,z}
      \le v_i(A_i)-v_i(A_{i'}).
  \]
  By \cref{def:copy-weighted-valuation-norm}, the copy-weighted valuation norm
  is a real square root and is therefore nonnegative. Multiplying the lower
  bound for $\alpha^*$ by this norm and substituting it in the preceding
  inequality gives exactly the asserted estimate for every ordered pair of
  distinct groups. -/)
  (title := /-- Integral rounding with an explicit envy-gap loss -/)
  (latexEnv := "lemma")]
lemma rounded_allocation_gap_lower_bound {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (htheta : ∀ z, frobenius_threshold I ≤ I.copies z)
    (hdiv : ∀ z, group_size_gcd I ∣ I.copies z) :
    ∃ A : allocation Group ItemType, complete_allocation I A ∧
      ∀ i i', i ≠ i' →
        copy_weighted_valuation_norm I i *
              (minimum_copy_weighted_separation_squared I /
                (2 * (number_of_agents I : ℝ) * maximum_copy_normalized_item_value I)) -
            2 * (rounding_complexity I : ℝ) * maximum_item_value I i ≤
          bundle_value I A i i - bundle_value I A i i' := by
  obtain ⟨X, α, hfeasible, _, hlower, hshared⟩ :=
    sparse_optimal_fractional_allocation I hprofile hpositive
  obtain ⟨A, hcomplete, hgap⟩ :=
    three_phase_integral_rounding I hprofile hpositive htheta hdiv
      X α hfeasible hshared
  refine ⟨A, hcomplete, ?_⟩
  intro i i' hne
  have hnorm : 0 ≤ copy_weighted_valuation_norm I i := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlower hnorm
  exact le_trans (sub_le_sub_right hmul _) (hgap i i' hne)

@[blueprint "lem:envy-free-sufficient-condition"
  (statement := /-- Let $I$ be an admissible finite goods profile. Assume that,
  for every item type $z$, the copy count $k_z$ is positive, is at least the
  Frobenius threshold $\theta$, and is divisible by the gcd $g$ of the group
  sizes. If
  \[
  \widetilde v_{\max}(\mathbf k)\le
  \sqrt{\frac{\delta(\mathbf k)^2}{4nC}},
  \]
  where $n$ is the total number of agents, $C$ is the rounding complexity, and
  $\delta(\mathbf k)^2$ is the minimum copy-weighted squared separation over
  ordered pairs of distinct groups, then $I$ admits a complete integral
  allocation, equal within each group, that is envy-free. -/)
  (proof := /-- Apply \cref{lem:rounded-allocation-gap-lower-bound} to
  obtain a complete allocation $A$ satisfying its gap estimate. By
  \cref{def:goods-profile-assumptions, def:number-of-agents}, positivity of the
  group sizes gives $n>0$. The existence of two distinct groups and
  \cref{def:number-of-groups, def:rounding-complexity} give $d\ge2$ and
  $C>0$.

  For every group $i$, positivity of the copy counts and of the unit valuation
  norm implies, by \cref{def:copy-weighted-valuation-norm}, that
  $\lVert v_i(\mathbf k)\rVert_2>0$. Nonnegativity of the valuations and
  positivity of the distinguished group's unit norm provide an item type of
  strictly positive value. It follows from
  \cref{def:copy-weighted-normalized-value,
  def:maximum-copy-normalized-item-value} that
  $\widetilde v_{\max}(\mathbf k)>0$.

  All factors in the denominator of the assumed bound are therefore positive.
  Squaring that bound and multiplying by $4nC$ yields
  \[
    4nC\widetilde v_{\max}(\mathbf k)^2
      \le \delta(\mathbf k)^2.
  \]
  Division by the positive number
  $2n\widetilde v_{\max}(\mathbf k)$ gives
  \[
    2C\widetilde v_{\max}(\mathbf k)
      \le
    \frac{\delta(\mathbf k)^2}
      {2n\widetilde v_{\max}(\mathbf k)}.
  \]

  For every group $i$ and item type $z$, the definitions of the normalized
  coordinate and its global maximum give
  \[
    v_{i,z}\le
    \lVert v_i(\mathbf k)\rVert_2
      \widetilde v_{\max}(\mathbf k).
  \]
  Taking the maximum over $z$ using \cref{def:maximum-item-value}, multiplying
  the preceding ratio inequality by the positive copy-weighted norm, and
  combining the two estimates shows
  \[
    2C\max_z v_{i,z}\le
    \lVert v_i(\mathbf k)\rVert_2
      \frac{\delta(\mathbf k)^2}
        {2n\widetilde v_{\max}(\mathbf k)}.
  \]
  Thus the lower bound in
  \cref{lem:rounded-allocation-gap-lower-bound} is nonnegative whenever
  $i\ne i'$, so $v_i(A_i)\ge v_i(A_{i'})$. For $i=i'$, the same inequality is
  reflexive. Hence $A$ is envy-free and, together with its completeness,
  witnesses \cref{def:admits-envy-free-allocation}. -/)
  (title := /-- Sufficient normalized-value condition for envy-freeness -/)
  (latexEnv := "lemma")]
lemma envy_free_sufficient_condition {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (htheta : ∀ z, frobenius_threshold I ≤ I.copies z)
    (hdiv : ∀ z, group_size_gcd I ∣ I.copies z)
    (hsmall : maximum_copy_normalized_item_value I ≤
      Real.sqrt (minimum_copy_weighted_separation_squared I /
        ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ))) :
    admits_envy_free_allocation I := by
  classical
  obtain ⟨A, hcomplete, hgap⟩ :=
    rounded_allocation_gap_lower_bound I hprofile hpositive htheta hdiv
  refine ⟨A, hcomplete, ?_⟩
  rcases hprofile with
    ⟨hsize, _, _, hvalue, hunitnorm, hgroups, _⟩
  have hn_nat : 0 < number_of_agents I := by
    unfold number_of_agents
    exact Finset.sum_pos' (fun i _ => Nat.zero_le (I.groupSize i))
      ⟨I.smallestGroup, Finset.mem_univ _, hsize I.smallestGroup⟩
  have hn : 0 < (number_of_agents I : ℝ) := by
    exact_mod_cast hn_nat
  have hd : 1 < number_of_groups I := by
    unfold number_of_groups
    exact Fintype.one_lt_card_iff.mpr hgroups
  have hgroup_term :
      0 < number_of_groups I * (number_of_groups I - 1) := by
    exact Nat.mul_pos (by omega) (Nat.sub_pos_iff_lt.mpr hd)
  have hcomplexity_nat : 0 < rounding_complexity I := by
    unfold rounding_complexity
    exact Nat.add_pos_left hgroup_term _
  have hcomplexity : 0 < (rounding_complexity I : ℝ) := by
    exact_mod_cast hcomplexity_nat
  have hcopy_sum_pos (i : Group) :
      0 < ∑ z, (I.copies z : ℝ) * (I.valuation i z) ^ 2 := by
    have hu : 0 < ∑ z, (I.valuation i z) ^ 2 :=
      Real.sqrt_pos.mp (hunitnorm i)
    refine lt_of_lt_of_le hu (Finset.sum_le_sum fun z _ => ?_)
    have hc : (1 : ℝ) ≤ I.copies z := by
      exact_mod_cast hpositive z
    nlinarith [sq_nonneg (I.valuation i z)]
  have hcopy_norm (i : Group) :
      0 < copy_weighted_valuation_norm I i := by
    rw [copy_weighted_valuation_norm]
    exact Real.sqrt_pos.mpr (hcopy_sum_pos i)
  have hnormalized_le (i : Group) (z : ItemType) :
      copy_weighted_normalized_value I i z ≤
        maximum_copy_normalized_item_value I := by
    simpa [maximum_copy_normalized_item_value] using
      (Finset.le_sup'
        (s := (Finset.univ.product Finset.univ : Finset (Group × ItemType)))
        (f := fun p => copy_weighted_normalized_value I p.1 p.2)
        (by simp : (i, z) ∈
          (Finset.univ.product Finset.univ : Finset (Group × ItemType))))
  have hsome_value_pos :
      ∃ z : ItemType, 0 < I.valuation I.smallestGroup z := by
    have hu : 0 < ∑ z, (I.valuation I.smallestGroup z) ^ 2 :=
      Real.sqrt_pos.mp (hunitnorm I.smallestGroup)
    obtain ⟨z, _, hz⟩ :=
      (Finset.sum_pos_iff_of_nonneg
        (fun z (_ : z ∈ (Finset.univ : Finset ItemType)) =>
          sq_nonneg (I.valuation I.smallestGroup z))).mp hu
    exact ⟨z, by nlinarith [hvalue I.smallestGroup z]⟩
  have hmaximum_pos : 0 < maximum_copy_normalized_item_value I := by
    obtain ⟨z, hz⟩ := hsome_value_pos
    have hz' :
        0 < copy_weighted_normalized_value I I.smallestGroup z := by
      rw [copy_weighted_normalized_value]
      exact div_pos hz (hcopy_norm I.smallestGroup)
    exact lt_of_lt_of_le hz' (hnormalized_le I.smallestGroup z)
  have hbound_den :
      0 < ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) := by
    positivity
  have hsqrt_pos :
      0 < Real.sqrt (minimum_copy_weighted_separation_squared I /
        ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ)) :=
    lt_of_lt_of_le hmaximum_pos hsmall
  have hsqrt_sq :
      (Real.sqrt (minimum_copy_weighted_separation_squared I /
        ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ))) ^ 2 =
        minimum_copy_weighted_separation_squared I /
          ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) := by
    exact Real.sq_sqrt (Real.sqrt_pos.mp hsqrt_pos).le
  have hmaximum_sq :
      (maximum_copy_normalized_item_value I) ^ 2 ≤
        minimum_copy_weighted_separation_squared I /
          ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) := by
    have hsum_nonneg :
        0 ≤ Real.sqrt (minimum_copy_weighted_separation_squared I /
            ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ)) +
          maximum_copy_normalized_item_value I := by
      positivity
    have hproduct :=
      mul_nonneg (sub_nonneg.mpr hsmall) hsum_nonneg
    nlinarith
  have hscaled :
      ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) *
          (maximum_copy_normalized_item_value I) ^ 2 ≤
        minimum_copy_weighted_separation_squared I := by
    simpa [mul_comm] using (le_div_iff₀ hbound_den).mp hmaximum_sq
  have hkey :
      4 * (number_of_agents I : ℝ) * (rounding_complexity I : ℝ) *
          (maximum_copy_normalized_item_value I) ^ 2 ≤
        minimum_copy_weighted_separation_squared I := by
    norm_num at hscaled ⊢
    exact hscaled
  intro i i'
  by_cases hii' : i = i'
  · subst i'
    exact le_rfl
  have hitem :
      maximum_item_value I i ≤
        copy_weighted_valuation_norm I i *
          maximum_copy_normalized_item_value I := by
    rw [maximum_item_value]
    apply Finset.sup'_le
    intro z _
    have hvaluation :
        I.valuation i z =
          copy_weighted_valuation_norm I i *
            copy_weighted_normalized_value I i z := by
      rw [copy_weighted_normalized_value]
      field_simp [ne_of_gt (hcopy_norm i)]
    rw [hvaluation]
    exact mul_le_mul_of_nonneg_left (hnormalized_le i z)
      (le_of_lt (hcopy_norm i))
  have hgap_ratio :
      2 * (rounding_complexity I : ℝ) *
          maximum_copy_normalized_item_value I ≤
        minimum_copy_weighted_separation_squared I /
          (2 * (number_of_agents I : ℝ) *
            maximum_copy_normalized_item_value I) := by
    rw [le_div_iff₀ (by positivity :
      0 < 2 * (number_of_agents I : ℝ) *
        maximum_copy_normalized_item_value I)]
    nlinarith
  have hloss :
      2 * (rounding_complexity I : ℝ) * maximum_item_value I i ≤
        copy_weighted_valuation_norm I i *
          (minimum_copy_weighted_separation_squared I /
            (2 * (number_of_agents I : ℝ) *
              maximum_copy_normalized_item_value I)) := by
    calc
      2 * (rounding_complexity I : ℝ) * maximum_item_value I i ≤
          2 * (rounding_complexity I : ℝ) *
            (copy_weighted_valuation_norm I i *
              maximum_copy_normalized_item_value I) :=
        mul_le_mul_of_nonneg_left hitem (by positivity)
      _ = copy_weighted_valuation_norm I i *
          (2 * (rounding_complexity I : ℝ) *
            maximum_copy_normalized_item_value I) := by ring
      _ ≤ copy_weighted_valuation_norm I i *
          (minimum_copy_weighted_separation_squared I /
            (2 * (number_of_agents I : ℝ) *
              maximum_copy_normalized_item_value I)) :=
        mul_le_mul_of_nonneg_left hgap_ratio
          (le_of_lt (hcopy_norm i))
  have hnonnegative :
      0 ≤ copy_weighted_valuation_norm I i *
            (minimum_copy_weighted_separation_squared I /
              (2 * (number_of_agents I : ℝ) *
                maximum_copy_normalized_item_value I)) -
          2 * (rounding_complexity I : ℝ) * maximum_item_value I i :=
    sub_nonneg.mpr hloss
  exact sub_nonneg.mp (hnonnegative.trans (hgap i i' hii'))

@[blueprint "lem:copy-window-reduction"
  (statement := /-- Let $I$ be a finite grouped goods instance satisfying the goods-profile assumptions. Write $n$ for its total number of agents, $g$ for the greatest common divisor of its group sizes, and $\mu$ for its advertised copy lower bound. Suppose that, for every item type $z$, the copy count $k_z$ is positive, satisfies $\mu\le k_z$, and is divisible by $g$. Then there exist functions $r$ and $q$ from the item types to $\mathbb{N}$ such that, for every $z$,
  \[
  0<r_z,\qquad \mu\le r_z<\mu+n,\qquad g\mid r_z,
  \qquad\text{and}\qquad k_z=r_z+q_zn.
  \]
  Moreover, if the instance obtained from $I$ by replacing its copy vector by $r$ admits a complete integral envy-free allocation that is equal within each group, then $I$ admits such an allocation. -/)
  (proof := /-- By \cref{def:goods-profile-assumptions, def:number-of-agents}, every group size is positive and hence $n>0$. The same profile assumptions make every squared unit separation positive. The set of ordered pairs of distinct groups is nonempty, so \cref{def:minimum-unit-separation-squared} and \cref{def:unit-separation-squared, def:unit-normalized-value, def:unit-valuation-norm} imply that the minimum squared separation is positive. Since the distinguished group makes the number of groups positive, \cref{def:number-of-groups, def:advertised-copy-complexity, def:advertised-copy-lower-bound} then give $\mu>0$.

Put $c=\lceil\mu\rceil_{\mathbb N}$ and, for every item type $z$, define
  \[
  r_z=c+((k_z-c)\bmod n),\qquad
  q_z=\left\lfloor\frac{k_z-c}{n}\right\rfloor.
  \]
The hypothesis $\mu\le k_z$ gives $c\le k_z$. The division algorithm therefore yields
$k_z=r_z+q_zn$. Since $c>0$, also $r_z>0$. The natural-ceiling inequalities give
$\mu\le c<\mu+1$, while the remainder lies in $\{0,\ldots,n-1\}$; consequently
$\mu\le r_z<\mu+n$.

By \cref{def:group-size-gcd, def:number-of-agents}, $g$ divides every group size and hence divides their sum $n$. Thus $g$ divides $q_zn$; together with $g\mid k_z$ and
$k_z=r_z+q_zn$, this proves $g\mid r_z$.

Finally, suppose that the residual instance from \cref{def:instance-with-copies} admits an allocation $A$ in the sense of \cref{def:admits-envy-free-allocation}. Define
$A'_{i,z}=A_{i,z}+q_z$. For each $z$, \cref{def:complete-allocation} gives
  \[
  \sum_i n_iA'_{i,z}
  =r_z+\left(\sum_i n_i\right)q_z
  =r_z+nq_z=k_z,
  \]
so $A'$ is complete for $I$. For any evaluating group $i$, expanding
\cref{def:bundle-value, def:envy-free-allocation} adds the same quantity
$\sum_zv_{i,z}q_z$ to the values of both compared bundles. Hence every envy inequality for $A$ is preserved by $A'$, and $I$ admits a complete envy-free allocation. -/)
  (title := /-- Reduction to a bounded copy window -/)
  (latexEnv := "lemma")]
lemma copy_window_reduction {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (hbound : ∀ z, advertised_copy_lower_bound I ≤ (I.copies z : ℝ))
    (hdiv : ∀ z, group_size_gcd I ∣ I.copies z) :
    ∃ r q : ItemType → ℕ,
      (∀ z, 0 < r z) ∧
      (∀ z, advertised_copy_lower_bound I ≤ (r z : ℝ)) ∧
      (∀ z, (r z : ℝ) <
        advertised_copy_lower_bound I + number_of_agents I) ∧
      (∀ z, group_size_gcd I ∣ r z) ∧
      (∀ z, I.copies z = r z + q z * number_of_agents I) ∧
      (admits_envy_free_allocation (instance_with_copies I r) →
        admits_envy_free_allocation I) := by
  classical
  have hn : 0 < number_of_agents I := by
    rw [number_of_agents]
    exact Finset.sum_pos (fun i _ => hprofile.1 i)
      ⟨I.smallestGroup, Finset.mem_univ _⟩
  have hsep_pos : 0 < minimum_unit_separation_squared I := by
    simp only [minimum_unit_separation_squared]
    split_ifs with hpairs
    · rw [Finset.lt_inf'_iff]
      intro p hp
      simpa [unit_separation_squared, unit_normalized_value, unit_valuation_norm] using
        hprofile.2.2.2.2.2.2 p.1 p.2 (by simpa using (Finset.mem_filter.mp hp).2)
    · exfalso
      apply hpairs
      obtain ⟨i, i', hne⟩ := hprofile.2.2.2.2.2.1
      exact ⟨(i, i'), by simp [hne]⟩
  have hd : 0 < number_of_groups I := by
    exact Fintype.card_pos_iff.mpr ⟨I.smallestGroup⟩
  have hcplx : 0 < advertised_copy_complexity I := by
    unfold advertised_copy_complexity
    positivity
  have hmu_pos : 0 < advertised_copy_lower_bound I := by
    unfold advertised_copy_lower_bound
    exact div_pos (by positivity) hsep_pos
  let c : ℕ := ⌈advertised_copy_lower_bound I⌉₊
  let r : ItemType → ℕ := fun z =>
    c + (I.copies z - c) % number_of_agents I
  let q : ItemType → ℕ := fun z =>
    (I.copies z - c) / number_of_agents I
  have hcpos : 0 < c := by
    dsimp [c]
    exact Nat.ceil_pos.mpr hmu_pos
  have hcle (z : ItemType) : c ≤ I.copies z := by
    dsimp [c]
    exact Nat.ceil_le.mpr (hbound z)
  have hcopy (z : ItemType) :
      I.copies z = r z + q z * number_of_agents I := by
    dsimp [r, q]
    symm
    rw [Nat.add_assoc, Nat.mul_comm ((I.copies z - c) / number_of_agents I),
      Nat.mod_add_div, Nat.add_sub_of_le (hcle z)]
  have hgn : group_size_gcd I ∣ number_of_agents I := by
    rw [group_size_gcd, number_of_agents]
    exact Finset.dvd_sum (fun i _ => Finset.gcd_dvd (Finset.mem_univ i))
  refine ⟨r, q, ?_, ?_, ?_, ?_, hcopy, ?_⟩
  · intro z
    dsimp [r]
    omega
  · intro z
    have hcr : c ≤ r z := by
      dsimp [r]
      omega
    calc
      advertised_copy_lower_bound I ≤ (c : ℝ) := by
        dsimp [c]
        exact Nat.le_ceil _
      _ ≤ (r z : ℝ) := by exact_mod_cast hcr
  · intro z
    have hmod : (I.copies z - c) % number_of_agents I < number_of_agents I :=
      Nat.mod_lt _ hn
    have hnat : r z + 1 ≤ c + number_of_agents I := by
      dsimp [r]
      omega
    have hcast :
        (r z : ℝ) + 1 ≤ (c : ℝ) + number_of_agents I := by
      exact_mod_cast hnat
    have hceil :
        (c : ℝ) < advertised_copy_lower_bound I + 1 := by
      dsimp [c]
      exact Nat.ceil_lt_add_one hmu_pos.le
    linarith
  · intro z
    have hround : group_size_gcd I ∣ q z * number_of_agents I :=
      dvd_mul_of_dvd_right hgn _
    apply (Nat.dvd_add_iff_left hround).mpr
    rw [← hcopy z]
    exact hdiv z
  · rintro ⟨A, hcomplete, henvy⟩
    refine ⟨fun i z => A i z + q z, ?_, ?_⟩
    · intro z
      have hres : (∑ i, I.groupSize i * A i z) = r z := hcomplete z
      calc
        ∑ i, I.groupSize i * (A i z + q z) =
            (∑ i, I.groupSize i * A i z) + ∑ i, I.groupSize i * q z := by
              simp only [Nat.mul_add, Finset.sum_add_distrib]
        _ = r z + number_of_agents I * q z := by
              rw [hres, number_of_agents, Finset.sum_mul]
        _ = r z + q z * number_of_agents I := by
              rw [Nat.mul_comm]
        _ = I.copies z := (hcopy z).symm
    · intro i i'
      have henvy' :
          (∑ z, I.valuation i z * (A i' z : ℝ)) ≤
            ∑ z, I.valuation i z * (A i z : ℝ) := by
        simpa only [bundle_value, instance_with_copies] using henvy i i'
      simp only [bundle_value, instance_with_copies, Nat.cast_add, mul_add,
        Finset.sum_add_distrib]
      linarith

@[blueprint "lem:advertised-bound-at-least-threshold"
  (statement := /-- Let $I$ be a fair-goods instance with finite sets of groups and item types. If $I$ satisfies the goods-profile assumptions, then its advertised real copy lower bound is at least its Frobenius threshold $\theta$. -/)
  (proof := /-- By \cref{def:goods-profile-assumptions}, the unit-copy valuation norm of every group is positive, at least one ordered pair of distinct groups exists, and every such pair has positive squared separation. Expanding \cref{def:unit-normalized-value, def:unit-valuation-norm} shows that the squares of the normalized coordinates of each group sum to $1$. The pointwise inequality $(a-b)^2\le 2a^2+2b^2$ and \cref{def:unit-separation-squared} therefore bound every squared separation by $4$. Thus \cref{def:minimum-unit-separation-squared} gives a minimum $delta^2$ satisfying $0<\delta^2\le4$.

  The positive group sizes in \cref{def:goods-profile-assumptions}, together with \cref{def:number-of-agents, def:number-of-groups}, imply $n\ge d$ and $n\ge1$. The distinguished item type in \cref{def:fair-goods-instance} and \cref{def:number-of-types} imply $t\ge1$, while the largest distinguished group has positive size. Hence natural-number subtraction gives
  \[
  \theta\le \theta+n+n_d-d-1.
  \]
  It follows from \cref{def:advertised-copy-complexity} that $	heta\le d^2+t(\theta+n+n_d-d-1)$ and consequently that $	heta\le n\bigl(d^2+t(\theta+n+n_d-d-1)\bigr)$. Therefore
  \[
  \theta\delta^2\le4\theta\le
  4n\bigl(d^2+t(\theta+n+n_d-d-1)\bigr).
  \]
  Dividing by the positive number $delta^2$ and applying \cref{def:advertised-copy-lower-bound} yields the asserted inequality. -/)
  (title := /-- The advertised bound dominates the Frobenius threshold -/)
  (latexEnv := "lemma")]
lemma advertised_bound_at_least_threshold {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I) :
    (frobenius_threshold I : ℝ) ≤ advertised_copy_lower_bound I := by
  classical
  rcases hprofile with
    ⟨hgroup_pos, hsmall, hlarge, hvaluation_nonnegative, hnorm_pos,
      hpairs_exist, hseparation_pos⟩
  have hunit_norm (i : Group) :
      ∑ z, (unit_normalized_value I i z) ^ 2 = 1 := by
    have hsum_pos : 0 < ∑ z, (I.valuation i z) ^ 2 :=
      (Real.sqrt_pos).mp (hnorm_pos i)
    simp only [unit_normalized_value, unit_valuation_norm]
    simp_rw [div_pow]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, Real.sq_sqrt (le_of_lt hsum_pos),
      mul_inv_cancel₀ (ne_of_gt hsum_pos)]
  have hseparation_le (i i' : Group) : unit_separation_squared I i i' ≤ 4 := by
    unfold unit_separation_squared
    calc
      ∑ z, (unit_normalized_value I i z -
          unit_normalized_value I i' z) ^ 2 ≤
          ∑ z, (2 * (unit_normalized_value I i z) ^ 2 +
            2 * (unit_normalized_value I i' z) ^ 2) := by
        apply Finset.sum_le_sum
        intro z hz
        nlinarith [sq_nonneg (unit_normalized_value I i z +
          unit_normalized_value I i' z)]
      _ = 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hunit_norm i, hunit_norm i']
        norm_num
  have hpairs : ((Finset.univ.product Finset.univ).filter
      (fun p : Group × Group => p.1 ≠ p.2)).Nonempty := by
    rcases hpairs_exist with ⟨i, i', hii'⟩
    refine ⟨(i, i'), ?_⟩
    simp [hii']
  have hminimum_pos : 0 < minimum_unit_separation_squared I := by
    simp only [minimum_unit_separation_squared, dif_pos hpairs]
    obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_inf' hpairs
      (fun p => unit_separation_squared I p.1 p.2)
    rw [heq]
    apply hseparation_pos
    simpa using hp
  have hminimum_le : minimum_unit_separation_squared I ≤ 4 := by
    simp only [minimum_unit_separation_squared, dif_pos hpairs]
    obtain ⟨i, i', hii'⟩ := hpairs_exist
    calc
      ((Finset.univ.product Finset.univ).filter
          (fun p : Group × Group => p.1 ≠ p.2)).inf' hpairs
          (fun p => unit_separation_squared I p.1 p.2) ≤
          unit_separation_squared I i i' := by
        exact Finset.inf'_le
          (s := (Finset.univ.product Finset.univ).filter
            (fun p : Group × Group => p.1 ≠ p.2))
          (b := (i, i'))
          (fun p : Group × Group => unit_separation_squared I p.1 p.2)
          (by simp [hii'])
      _ ≤ 4 := hseparation_le i i'
  have hagents_ge_groups : number_of_groups I ≤ number_of_agents I := by
    unfold number_of_groups number_of_agents
    calc
      Fintype.card Group = ∑ _ : Group, 1 := by simp
      _ ≤ ∑ i : Group, I.groupSize i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hgroup_pos i
  have hagents_pos : 1 ≤ number_of_agents I := by
    have hsize_le : I.groupSize I.smallestGroup ≤ number_of_agents I := by
      unfold number_of_agents
      apply Finset.single_le_sum
      · intro i hi
        exact Nat.zero_le (I.groupSize i)
      · simp
    exact le_trans (hgroup_pos I.smallestGroup) hsize_le
  have htypes_pos : 1 ≤ number_of_types I := by
    unfold number_of_types
    exact Fintype.card_pos_iff.mpr ⟨I.someType⟩
  have hinner : frobenius_threshold I ≤
      frobenius_threshold I + number_of_agents I +
        I.groupSize I.largestGroup - number_of_groups I - 1 := by
    have hlargest_pos := hgroup_pos I.largestGroup
    omega
  have hcomplexity : frobenius_threshold I ≤ advertised_copy_complexity I := by
    have hproduct : frobenius_threshold I ≤ number_of_types I *
        (frobenius_threshold I + number_of_agents I +
          I.groupSize I.largestGroup - number_of_groups I - 1) := by
      simpa using Nat.mul_le_mul htypes_pos hinner
    unfold advertised_copy_complexity
    omega
  have hthreshold_numerator : frobenius_threshold I ≤
      number_of_agents I * advertised_copy_complexity I := by
    calc
      frobenius_threshold I ≤ advertised_copy_complexity I := hcomplexity
      _ = 1 * advertised_copy_complexity I := by simp
      _ ≤ number_of_agents I * advertised_copy_complexity I :=
        Nat.mul_le_mul_right (advertised_copy_complexity I) hagents_pos
  rw [advertised_copy_lower_bound, le_div_iff₀ hminimum_pos]
  calc
    (frobenius_threshold I : ℝ) * minimum_unit_separation_squared I ≤
        (frobenius_threshold I : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left hminimum_le (Nat.cast_nonneg _)
    _ ≤ ((number_of_agents I * advertised_copy_complexity I : ℕ) : ℝ) * 4 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hthreshold_numerator)
        (by norm_num)
    _ = ((4 * number_of_agents I * advertised_copy_complexity I : ℕ) : ℝ) := by
      push_cast
      ring

@[blueprint "lem:copy-distance-coefficient-distortion"
  (statement := /-- Let $u$ and $v$ be unit vectors in a finite-dimensional real Euclidean space. If $0\le q\le a,b\le1$, then
  \[
  q\lVert u-v\rVert_2-(1-q)\le\lVert au-bv\rVert_2.
  \] -/)
  (proof := /-- If $a\le b$, write $au-bv=a(u-v)-(b-a)v$. Expanding the squared norm and applying the finite Cauchy--Schwarz inequality to the cross term, together with $\lVert v\rVert_2=1$, gives
  $\lVert au-bv\rVert_2\ge a\lVert u-v\rVert_2-(b-a)$ whenever the right-hand side is positive; if it is nonpositive, the inequality follows from nonnegativity of the norm. This lower bound is at least
  $q\lVert u-v\rVert_2-(1-q)$ because $a\ge q$, $b\le1$, and norms are nonnegative. If $b\le a$, exchange $u,a$ with $v,b$ and use invariance of the norm under negation. -/)
  (title := /-- Distortion under bounded normalization coefficients -/)
  (latexEnv := "lemma")]
lemma copy_distance_coefficient_distortion {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (q a b : ℝ)
    (hu : ∑ z, (u z) ^ 2 = 1) (hv : ∑ z, (v z) ^ 2 = 1)
    (hq : 0 ≤ q) (ha : q ≤ a) (ha' : a ≤ 1)
    (hb : q ≤ b) (hb' : b ≤ 1) :
    q * Real.sqrt (∑ z, (u z - v z) ^ 2) - (1 - q) ≤
      Real.sqrt (∑ z, (a * u z - b * v z) ^ 2) := by
  let D : ℝ := Real.sqrt (∑ z, (u z - v z) ^ 2)
  let E : ℝ := Real.sqrt (∑ z, (a * u z - b * v z) ^ 2)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  by_cases hnonpos : q * D - (1 - q) ≤ 0
  · change q * D - (1 - q) ≤ E
    exact hnonpos.trans hE0
  have hDsum0 : 0 ≤ ∑ z, (u z - v z) ^ 2 :=
    Finset.sum_nonneg fun z _ => sq_nonneg (u z - v z)
  have hEsum0 : 0 ≤ ∑ z, (a * u z - b * v z) ^ 2 :=
    Finset.sum_nonneg fun z _ => sq_nonneg (a * u z - b * v z)
  have hDsq : D ^ 2 = ∑ z, (u z - v z) ^ 2 := by
    exact Real.sq_sqrt hDsum0
  have hEsq : E ^ 2 = ∑ z, (a * u z - b * v z) ^ 2 := by
    exact Real.sq_sqrt hEsum0
  rcases le_total a b with hab | hba
  · have ha0 : 0 ≤ a := hq.trans ha
    have hc0 : 0 ≤ b - a := sub_nonneg.mpr hab
    have hcross : ∑ z, (u z - v z) * v z ≤ D := by
      have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun z => u z - v z) v
      simpa only [Finset.mem_univ, true_and, hv, Real.sqrt_one, mul_one] using hc
    have hexpand :
        ∑ z, (a * u z - b * v z) ^ 2 =
          a ^ 2 * (∑ z, (u z - v z) ^ 2) +
            (b - a) ^ 2 * (∑ z, (v z) ^ 2) -
              2 * a * (b - a) * (∑ z, (u z - v z) * v z) := by
      calc
        ∑ z, (a * u z - b * v z) ^ 2 =
            ∑ z, (a ^ 2 * (u z - v z) ^ 2 +
              (b - a) ^ 2 * (v z) ^ 2 -
                2 * a * (b - a) * ((u z - v z) * v z)) := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  ring
        _ = a ^ 2 * (∑ z, (u z - v z) ^ 2) +
            (b - a) ^ 2 * (∑ z, (v z) ^ 2) -
              2 * a * (b - a) * (∑ z, (u z - v z) * v z) := by
                simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  ← Finset.mul_sum]
    have hcrossprod :
        0 ≤ a * (b - a) * (D - ∑ z, (u z - v z) * v z) :=
      mul_nonneg (mul_nonneg ha0 hc0) (sub_nonneg.mpr hcross)
    have hbase :
        q * D - (1 - q) ≤ a * D - (b - a) := by
      have hprod : 0 ≤ (a - q) * D :=
        mul_nonneg (sub_nonneg.mpr ha) hD0
      nlinarith
    have hbasepos : 0 < a * D - (b - a) :=
      lt_of_lt_of_le (lt_of_not_ge hnonpos) hbase
    have hsquares : (a * D - (b - a)) ^ 2 ≤ E ^ 2 := by
      rw [hEsq, hexpand, hv]
      nlinarith
    have hroot : a * D - (b - a) ≤ E := by
      nlinarith
    change q * D - (1 - q) ≤ E
    exact hbase.trans hroot
  · have hb0 : 0 ≤ b := hq.trans hb
    have hc0 : 0 ≤ a - b := sub_nonneg.mpr hba
    have hrevsum :
        (∑ z, (v z - u z) ^ 2) = ∑ z, (u z - v z) ^ 2 := by
      apply Finset.sum_congr rfl
      intro z hz
      ring
    have hcross : ∑ z, (v z - u z) * u z ≤ D := by
      have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun z => v z - u z) u
      simpa only [Finset.mem_univ, true_and, hrevsum, hu, Real.sqrt_one, mul_one] using hc
    have hexpand :
        ∑ z, (a * u z - b * v z) ^ 2 =
          b ^ 2 * (∑ z, (v z - u z) ^ 2) +
            (a - b) ^ 2 * (∑ z, (u z) ^ 2) -
              2 * b * (a - b) * (∑ z, (v z - u z) * u z) := by
      calc
        ∑ z, (a * u z - b * v z) ^ 2 =
            ∑ z, (b ^ 2 * (v z - u z) ^ 2 +
              (a - b) ^ 2 * (u z) ^ 2 -
                2 * b * (a - b) * ((v z - u z) * u z)) := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  ring
        _ = b ^ 2 * (∑ z, (v z - u z) ^ 2) +
            (a - b) ^ 2 * (∑ z, (u z) ^ 2) -
              2 * b * (a - b) * (∑ z, (v z - u z) * u z) := by
                simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  ← Finset.mul_sum]
    have hcrossprod :
        0 ≤ b * (a - b) * (D - ∑ z, (v z - u z) * u z) :=
      mul_nonneg (mul_nonneg hb0 hc0) (sub_nonneg.mpr hcross)
    have hbase :
        q * D - (1 - q) ≤ b * D - (a - b) := by
      have hprod : 0 ≤ (b - q) * D :=
        mul_nonneg (sub_nonneg.mpr hb) hD0
      nlinarith
    have hbasepos : 0 < b * D - (a - b) :=
      lt_of_lt_of_le (lt_of_not_ge hnonpos) hbase
    have hsquares : (b * D - (a - b)) ^ 2 ≤ E ^ 2 := by
      rw [hEsq, hexpand, hrevsum, hu]
      nlinarith
    have hroot : b * D - (a - b) ≤ E := by
      nlinarith
    change q * D - (1 - q) ≤ E
    exact hbase.trans hroot

@[blueprint "lem:copy-distance-lower-bound"
  (statement := /-- Let $I$ be an admissible goods profile with finite group and item-type sets. Let $\alpha,\beta\in\mathbb R$ satisfy $0<\alpha\le\beta$, and suppose that $\alpha\le k_z\le\beta$ for every item type $z$. Then, for every pair of groups $i,i'$,
  \[
  \sqrt{\frac{\alpha}{\beta}}\,
  \lVert\widetilde v_i-\widetilde v_{i'}\rVert_2-
  \left(1-\sqrt{\frac{\alpha}{\beta}}\right)
  \le \lVert\widetilde v_i(\mathbf k)-\widetilde v_{i'}(\mathbf k)\rVert_2.
  \] -/)
  (proof := /-- By admissibility in \cref{def:goods-profile-assumptions}, every unit-copy valuation norm is positive. The copy window and the definitions in \cref{def:unit-valuation-norm, def:copy-weighted-valuation-norm} give, for every group $j$,
  \[
  \alpha\lVert v_j\rVert_2^2\le
  \lVert v_j(\mathbf k)\rVert_2^2\le
  \beta\lVert v_j\rVert_2^2.
  \]
  Hence the copy-weighted norm is positive. By \cref{def:unit-normalized-value}, the squared coordinates of $\widetilde v_j$ sum to one. Put
  $q=\sqrt{\alpha/\beta}$ and
  $a_j=\sqrt\alpha\,\lVert v_j\rVert_2/\lVert v_j(\mathbf k)\rVert_2$.
  Squaring nonnegative quantities in the preceding norm bounds yields
  $q\le a_j\le1$. Moreover, \cref{def:copy-weighted-normalized-value} gives
  $a_j\widetilde v_{j,z}=\sqrt\alpha\,\widetilde v_{j,z}(\mathbf k)$.
  Applying \cref{lem:copy-distance-coefficient-distortion} to groups $i,i'$ therefore bounds the left-hand side by
  \[
  \sqrt{\alpha\sum_z
    (\widetilde v_{i,z}(\mathbf k)-\widetilde v_{i',z}(\mathbf k))^2}.
  \]
  Since $k_z\ge\alpha$ termwise, this is at most the square root of the copy-weighted squared separation. The identifications with the two displayed separations are exactly \cref{def:unit-separation-squared, def:copy-weighted-separation-squared}. -/)
  (title := /-- Distortion of normalized distances under copies -/)
  (latexEnv := "lemma")]
lemma copy_distance_lower_bound {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I) (α β : ℝ)
    (hα : 0 < α) (hαβ : α ≤ β)
    (hlower : ∀ z, α ≤ (I.copies z : ℝ))
    (hupper : ∀ z, (I.copies z : ℝ) ≤ β) (i i' : Group) :
    Real.sqrt (α / β) * Real.sqrt (unit_separation_squared I i i') -
        (1 - Real.sqrt (α / β)) ≤
      Real.sqrt (copy_weighted_separation_squared I i i') := by
  rcases hprofile with ⟨hgroups, hsmall, hlarge, hvalues, hunit, hpairs, hsep⟩
  have hα0 : 0 ≤ α := le_of_lt hα
  have hβpos : 0 < β := lt_of_lt_of_le hα hαβ
  have hβ0 : 0 ≤ β := le_of_lt hβpos
  have hsα0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg _
  have hsαsq : (Real.sqrt α) ^ 2 = α := Real.sq_sqrt hα0
  have hratio0 : 0 ≤ α / β := div_nonneg hα0 hβ0
  have hq0 : 0 ≤ Real.sqrt (α / β) := Real.sqrt_nonneg _
  have hqsq : (Real.sqrt (α / β)) ^ 2 = α / β :=
    Real.sq_sqrt hratio0
  have hcoeff (j : Group) :
      (∑ z, (unit_normalized_value I j z) ^ 2 = 1) ∧
        0 < copy_weighted_valuation_norm I j ∧
        Real.sqrt (α / β) ≤
          Real.sqrt α * unit_valuation_norm I j /
            copy_weighted_valuation_norm I j ∧
        Real.sqrt α * unit_valuation_norm I j /
            copy_weighted_valuation_norm I j ≤ 1 := by
    have hUpos : 0 < unit_valuation_norm I j := by
      simpa only [unit_valuation_norm] using hunit j
    have hUsum0 : 0 ≤ ∑ z, (I.valuation j z) ^ 2 :=
      Finset.sum_nonneg fun z _ => sq_nonneg (I.valuation j z)
    have hUsq :
        (unit_valuation_norm I j) ^ 2 =
          ∑ z, (I.valuation j z) ^ 2 := by
      exact Real.sq_sqrt hUsum0
    have hUsumpos : 0 < ∑ z, (I.valuation j z) ^ 2 := by
      rw [← hUsq]
      positivity
    have hcopyLower :
        α * (∑ z, (I.valuation j z) ^ 2) ≤
          ∑ z, (I.copies z : ℝ) * (I.valuation j z) ^ 2 := by
      calc
        α * (∑ z, (I.valuation j z) ^ 2) =
            ∑ z, α * (I.valuation j z) ^ 2 := by
              rw [Finset.mul_sum]
        _ ≤ ∑ z, (I.copies z : ℝ) * (I.valuation j z) ^ 2 := by
          apply Finset.sum_le_sum
          intro z hz
          exact mul_le_mul_of_nonneg_right (hlower z) (sq_nonneg _)
    have hcopyUpper :
        (∑ z, (I.copies z : ℝ) * (I.valuation j z) ^ 2) ≤
          β * (∑ z, (I.valuation j z) ^ 2) := by
      calc
        (∑ z, (I.copies z : ℝ) * (I.valuation j z) ^ 2) ≤
            ∑ z, β * (I.valuation j z) ^ 2 := by
          apply Finset.sum_le_sum
          intro z hz
          exact mul_le_mul_of_nonneg_right (hupper z) (sq_nonneg _)
        _ = β * (∑ z, (I.valuation j z) ^ 2) := by
          rw [Finset.mul_sum]
    have hcopySum0 :
        0 ≤ ∑ z, (I.copies z : ℝ) * (I.valuation j z) ^ 2 := by
      exact Finset.sum_nonneg fun z _ =>
        mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hCsq :
        (copy_weighted_valuation_norm I j) ^ 2 =
          ∑ z, (I.copies z : ℝ) * (I.valuation j z) ^ 2 := by
      exact Real.sq_sqrt hcopySum0
    have hcopySumPos :
        0 < ∑ z, (I.copies z : ℝ) * (I.valuation j z) ^ 2 := by
      nlinarith [mul_pos hα hUsumpos]
    have hCpos : 0 < copy_weighted_valuation_norm I j := by
      exact Real.sqrt_pos.mpr hcopySumPos
    have hnormalized :
        ∑ z, (unit_normalized_value I j z) ^ 2 = 1 := by
      simp only [unit_normalized_value]
      simp_rw [div_pow]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← hUsq]
      field_simp
    have hscaledLower :
        (Real.sqrt α * unit_valuation_norm I j) ^ 2 ≤
          (copy_weighted_valuation_norm I j) ^ 2 := by
      rw [mul_pow, hsαsq, hUsq, hCsq]
      exact hcopyLower
    have haUpper :
        Real.sqrt α * unit_valuation_norm I j /
            copy_weighted_valuation_norm I j ≤ 1 := by
      apply (div_le_iff₀ hCpos).2
      have hU0 : 0 ≤ unit_valuation_norm I j := le_of_lt hUpos
      nlinarith
    have hscaledUpper :
        (α / β) * (copy_weighted_valuation_norm I j) ^ 2 ≤
          α * (unit_valuation_norm I j) ^ 2 := by
      calc
        (α / β) * (copy_weighted_valuation_norm I j) ^ 2 =
            (α / β) *
              (∑ z, (I.copies z : ℝ) * (I.valuation j z) ^ 2) := by
                rw [hCsq]
        _ ≤ (α / β) *
            (β * (∑ z, (I.valuation j z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcopyUpper hratio0
        _ = α * (unit_valuation_norm I j) ^ 2 := by
          rw [hUsq]
          field_simp
    have haLower :
        Real.sqrt (α / β) ≤
          Real.sqrt α * unit_valuation_norm I j /
            copy_weighted_valuation_norm I j := by
      apply (le_div_iff₀ hCpos).2
      have hC0 : 0 ≤ copy_weighted_valuation_norm I j := le_of_lt hCpos
      have hU0 : 0 ≤ unit_valuation_norm I j := le_of_lt hUpos
      have hsquares :
          (Real.sqrt (α / β) * copy_weighted_valuation_norm I j) ^ 2 ≤
            (Real.sqrt α * unit_valuation_norm I j) ^ 2 := by
        rw [mul_pow, hqsq, mul_pow, hsαsq]
        exact hscaledUpper
      exact (sq_le_sq₀ (mul_nonneg hq0 hC0) (mul_nonneg hsα0 hU0)).mp hsquares
    exact ⟨hnormalized, hCpos, haLower, haUpper⟩
  rcases hcoeff i with ⟨hiunit, hiCpos, hiaLower, hiaUpper⟩
  rcases hcoeff i' with ⟨hi'unit, hi'Cpos, hi'aLower, hi'aUpper⟩
  have hiUpos : 0 < unit_valuation_norm I i := by
    simpa only [unit_valuation_norm] using hunit i
  have hi'Upos : 0 < unit_valuation_norm I i' := by
    simpa only [unit_valuation_norm] using hunit i'
  have hscale (j : Group) (z : ItemType)
      (hUpos : 0 < unit_valuation_norm I j)
      (hCpos : 0 < copy_weighted_valuation_norm I j) :
      (Real.sqrt α * unit_valuation_norm I j /
          copy_weighted_valuation_norm I j) *
          unit_normalized_value I j z =
        Real.sqrt α * copy_weighted_normalized_value I j z := by
    unfold unit_normalized_value copy_weighted_normalized_value
    field_simp [ne_of_gt hUpos, ne_of_gt hCpos]
  have hdist := copy_distance_coefficient_distortion
    (fun z => unit_normalized_value I i z)
    (fun z => unit_normalized_value I i' z)
    (Real.sqrt (α / β))
    (Real.sqrt α * unit_valuation_norm I i /
      copy_weighted_valuation_norm I i)
    (Real.sqrt α * unit_valuation_norm I i' /
      copy_weighted_valuation_norm I i')
    hiunit hi'unit hq0 hiaLower hiaUpper hi'aLower hi'aUpper
  have hscaledSum :
      (∑ z,
          ((Real.sqrt α * unit_valuation_norm I i /
                copy_weighted_valuation_norm I i) *
                unit_normalized_value I i z -
            (Real.sqrt α * unit_valuation_norm I i' /
                copy_weighted_valuation_norm I i') *
                unit_normalized_value I i' z) ^ 2) =
        α * (∑ z,
          (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z) ^ 2) := by
    calc
      _ = ∑ z,
          (Real.sqrt α * copy_weighted_normalized_value I i z -
            Real.sqrt α * copy_weighted_normalized_value I i' z) ^ 2 := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [hscale i z hiUpos hiCpos, hscale i' z hi'Upos hi'Cpos]
      _ = α * (∑ z,
          (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z) ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z hz
              nlinarith
  rw [hscaledSum] at hdist
  have hcopyLower :
      α * (∑ z,
          (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z) ^ 2) ≤
        copy_weighted_separation_squared I i i' := by
    unfold copy_weighted_separation_squared
    calc
      α * (∑ z,
          (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z) ^ 2) =
          ∑ z, α *
            (copy_weighted_normalized_value I i z -
              copy_weighted_normalized_value I i' z) ^ 2 := by
                rw [Finset.mul_sum]
      _ ≤ ∑ z, (I.copies z : ℝ) *
          (copy_weighted_normalized_value I i z -
            copy_weighted_normalized_value I i' z) ^ 2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_right (hlower z) (sq_nonneg _)
  have hsqrtLower := Real.sqrt_le_sqrt hcopyLower
  unfold unit_separation_squared
  exact hdist.trans hsqrtLower

@[blueprint "lem:minimum-copy-distance-lower-bound"
  (statement := /-- Let $I$ be an admissible goods profile with finite group and item-type sets. Let $\alpha,\beta\in\mathbb R$ satisfy $0<\alpha\le\beta$, and suppose that $\alpha\le k_z\le\beta$ for every item type $z$. Then
  \[
  \sqrt{\frac{\alpha}{\beta}}\,
  \sqrt{\min_{i\ne i'}\lVert\widetilde v_i-\widetilde v_{i'}\rVert_2^2}
  -\left(1-\sqrt{\frac{\alpha}{\beta}}\right)
  \le
  \sqrt{\min_{i\ne i'}
    \lVert\widetilde v_i(\mathbf k)-\widetilde v_{i'}(\mathbf k)\rVert_2^2},
  \]
  where both minima range over ordered pairs of distinct groups. -/)
  (proof := /-- By admissibility in \cref{def:goods-profile-assumptions}, the finite set of ordered pairs of distinct groups is nonempty. Choose a pair $(i_0,i'_0)$ at which the copy-weighted squared separation is minimal. By \cref{def:minimum-unit-separation-squared},
  \[
  \min_{i\ne i'}\lVert\widetilde v_i-\widetilde v_{i'}\rVert_2^2
  \le \lVert\widetilde v_{i_0}-\widetilde v_{i'_0}\rVert_2^2.
  \]
  The square-root function is monotone, and its product with the nonnegative number $\sqrt{\alpha/\beta}$ is also monotone. Subtracting the common term $1-\sqrt{\alpha/\beta}$ and applying \cref{lem:copy-distance-lower-bound} to $(i_0,i'_0)$ therefore bounds the left-hand side by
  $\lVert\widetilde v_{i_0}(\mathbf k)-\widetilde v_{i'_0}(\mathbf k)\rVert_2$.
  By the choice of $(i_0,i'_0)$ and \cref{def:minimum-copy-weighted-separation-squared}, this last quantity is the right-hand side. -/)
  (title := /-- Minimum normalized-distance distortion -/)
  (latexEnv := "lemma")]
lemma minimum_copy_distance_lower_bound {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I) (α β : ℝ)
    (hα : 0 < α) (hαβ : α ≤ β)
    (hlower : ∀ z, α ≤ (I.copies z : ℝ))
    (hupper : ∀ z, (I.copies z : ℝ) ≤ β) :
    Real.sqrt (α / β) * Real.sqrt (minimum_unit_separation_squared I) -
        (1 - Real.sqrt (α / β)) ≤
      Real.sqrt (minimum_copy_weighted_separation_squared I) := by
  classical
  have hpairs : ((Finset.univ.product Finset.univ).filter
      (fun p : Group × Group => p.1 ≠ p.2)).Nonempty := by
    rcases hprofile.2.2.2.2.2.1 with ⟨i, i', hii'⟩
    exact ⟨(i, i'), by simp [hii']⟩
  obtain ⟨p, hp, hcopy_eq⟩ := Finset.exists_mem_eq_inf' hpairs
    (fun p => copy_weighted_separation_squared I p.1 p.2)
  have hunit_le : minimum_unit_separation_squared I ≤
      unit_separation_squared I p.1 p.2 := by
    simp only [minimum_unit_separation_squared, dif_pos hpairs]
    exact Finset.inf'_le
      (s := (Finset.univ.product Finset.univ).filter
        (fun p : Group × Group => p.1 ≠ p.2))
      (f := fun p => unit_separation_squared I p.1 p.2)
      (b := p) hp
  calc
    Real.sqrt (α / β) * Real.sqrt (minimum_unit_separation_squared I) -
        (1 - Real.sqrt (α / β)) ≤
        Real.sqrt (α / β) * Real.sqrt (unit_separation_squared I p.1 p.2) -
          (1 - Real.sqrt (α / β)) := by
      exact sub_le_sub_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hunit_le)
          (Real.sqrt_nonneg _)) _
    _ ≤ Real.sqrt (copy_weighted_separation_squared I p.1 p.2) :=
      copy_distance_lower_bound I hprofile α β hα hαβ hlower hupper p.1 p.2
    _ = Real.sqrt (minimum_copy_weighted_separation_squared I) := by
      rw [minimum_copy_weighted_separation_squared, dif_pos hpairs, hcopy_eq]

@[blueprint "lem:scalar-square-root-lower-bound"
  (statement := /-- Let $a,b,x$ be nonnegative real numbers, with a quotient whose
  denominator is zero interpreted as zero. If $x\ge a(b+1)/(2b)$, then
  \[
  x\left(\sqrt{\frac{x}{x+a}}b-
  \left(1-\sqrt{\frac{x}{x+a}}\right)\right)^2
  \ge b^2x-ab(b+1).
  \] -/)
  (proof := /-- If $b=0$, the left-hand side is zero and the right-hand side is
  nonnegative. If $x=0$, the assertion reduces to $-ab(b+1)\leq 0$. Hence assume
  $b,x>0$. Clearing the positive denominator $2b$ in the hypothesis gives
  $a(b+1)\leq 2bx$. Since $b+1>0$, comparison with
  $2x(b+1)$ yields $a\leq 2x$. Consequently $0\leq a/(2x)\leq 1$, and
  \[
  \frac{x}{x+a}-\left(1-\frac{a}{2x}\right)^2
  =\frac{a^2(3x-a)}{4x^2(x+a)}\geq 0.
  \]
  Both $1-a/(2x)$ and the square root are nonnegative, so this identity implies
  $1-a/(2x)\leq\sqrt{x/(x+a)}$. The original hypothesis also gives
  $0\leq b-a(b+1)/(2x)$. Multiplying the square-root bound by $b+1$ and
  subtracting $1$ therefore gives an inequality between two nonnegative quantities,
  \[
  b-\frac{a(b+1)}{2x}\leq
  \sqrt{\frac{x}{x+a}}\,b-\left(1-\sqrt{\frac{x}{x+a}}\right).
  \]
  Squaring preserves this inequality. Finally,
  \[
  x\left(b-\frac{a(b+1)}{2x}\right)^2
  =b^2x-ab(b+1)+\frac{(a(b+1))^2}{4x}
  \geq b^2x-ab(b+1).
  \]
  Multiplication of the squared comparison by $x\geq0$ and transitivity prove the
  claim. -/)
  (title := /-- A scalar lower bound for the copy estimate -/)
  (latexEnv := "lemma")]
lemma scalar_square_root_lower_bound (a b x : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hlarge : a * (b + 1) / (2 * b) ≤ x) :
    b ^ 2 * x - a * b * (b + 1) ≤
      x * (Real.sqrt (x / (x + a)) * b -
        (1 - Real.sqrt (x / (x + a)))) ^ 2 := by
  by_cases hbzero : b = 0
  · subst b
    norm_num
    positivity
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
  by_cases hxzero : x = 0
  · subst x
    norm_num
    positivity
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hdenpos : 0 < x + a := by positivity
  have hcross : a * (b + 1) ≤ x * (2 * b) :=
    (div_le_iff₀ (by positivity : 0 < 2 * b)).mp hlarge
  have hbaddpos : 0 < b + 1 := by positivity
  have hcross' : a * (b + 1) ≤ (2 * x) * (b + 1) := by
    nlinarith
  have hatwo : a ≤ 2 * x := (mul_le_mul_iff_of_pos_right hbaddpos).mp hcross'
  have hthree : 0 ≤ 3 * x - a := by nlinarith
  have hquotle : a / (2 * x) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * x)).mpr
    nlinarith
  have hsqrt_lower : 1 - a / (2 * x) ≤ Real.sqrt (x / (x + a)) := by
    apply (Real.le_sqrt (by nlinarith) (by positivity)).mpr
    have hid :
        x / (x + a) - (1 - a / (2 * x)) ^ 2 =
          a ^ 2 * (3 * x - a) / (4 * x ^ 2 * (x + a)) := by
      field_simp [hxpos.ne', hdenpos.ne'] <;> ring
    have hrem : 0 ≤ a ^ 2 * (3 * x - a) / (4 * x ^ 2 * (x + a)) := by
      positivity
    nlinarith
  have hbase : 0 ≤ b - a * (b + 1) / (2 * x) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : 0 < 2 * x)).mpr
    nlinarith
  have hinner :
      b - a * (b + 1) / (2 * x) ≤
        Real.sqrt (x / (x + a)) * b -
          (1 - Real.sqrt (x / (x + a))) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt_lower (le_of_lt hbaddpos)
    calc
      b - a * (b + 1) / (2 * x) =
          (b + 1) * (1 - a / (2 * x)) - 1 := by ring
      _ ≤ (b + 1) * Real.sqrt (x / (x + a)) - 1 := sub_le_sub_right hmul 1
      _ = Real.sqrt (x / (x + a)) * b -
          (1 - Real.sqrt (x / (x + a))) := by ring
  have hsquares :
      (b - a * (b + 1) / (2 * x)) ^ 2 ≤
        (Real.sqrt (x / (x + a)) * b -
          (1 - Real.sqrt (x / (x + a)))) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hbase hinner
  have hid :
      x * (b - a * (b + 1) / (2 * x)) ^ 2 =
        b ^ 2 * x - a * b * (b + 1) +
          (a * (b + 1)) ^ 2 / (4 * x) := by
    field_simp [hxpos.ne'] <;> ring
  have hrem : 0 ≤ (a * (b + 1)) ^ 2 / (4 * x) := by positivity
  have hleft :
      b ^ 2 * x - a * b * (b + 1) ≤
        x * (b - a * (b + 1) / (2 * x)) ^ 2 := by
    nlinarith
  exact hleft.trans (mul_le_mul_of_nonneg_left hsquares hx)

@[blueprint "lem:advertised-copy-bound-positive"
  (statement := /-- Let $I$ be a grouped goods instance over finite group and item-type spaces. If $I$ satisfies the admissible goods-profile assumptions, then its advertised copy lower bound $\mu$ is strictly positive. -/)
  (proof := /-- Unpack the admissibility conditions in \cref{def:goods-profile-assumptions} and choose distinct groups $i$ and $i'$. Positivity of every group size and \cref{def:number-of-agents} give $n>0$, while the existence of $i$ and \cref{def:number-of-groups} give $d>0$. Consequently, the $d^2$ summand in \cref{def:advertised-copy-complexity} is positive, and hence so is the numerator $4n\bigl(d^2+t(\theta+n+n_d-d-1)\bigr)$. The ordered pair $(i,i')$ belongs to the finite set of distinct group pairs used in \cref{def:minimum-unit-separation-squared}, so this set is nonempty. By \cref{def:unit-separation-squared, def:unit-normalized-value, def:unit-valuation-norm} and admissibility, the squared separation attached to every member of that set is strictly positive; therefore its finite infimum is strictly positive. The quotient defining the advertised bound in \cref{def:advertised-copy-lower-bound} has positive numerator and denominator, and is thus strictly positive. -/)
  (title := /-- Positivity of the advertised copy bound -/)
  (latexEnv := "lemma")]
lemma advertised_copy_bound_positive {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I) :
    0 < advertised_copy_lower_bound I := by
  classical
  rcases hprofile with ⟨hsize, hsmall, hlarge, hvalue, hnorm, hex, hsep⟩
  rcases hex with ⟨i, i', hii'⟩
  have hn : 0 < number_of_agents I := by
    unfold number_of_agents
    exact Finset.sum_pos (fun j _ => hsize j) ⟨i, Finset.mem_univ i⟩
  have hd : 0 < number_of_groups I := by
    unfold number_of_groups
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  have hc : 0 < advertised_copy_complexity I := by
    unfold advertised_copy_complexity
    positivity
  unfold advertised_copy_lower_bound
  apply div_pos
  · norm_cast
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hn) hc
  · unfold minimum_unit_separation_squared
    dsimp only
    split
    · rw [Finset.lt_inf'_iff]
      intro p hp
      unfold unit_separation_squared unit_normalized_value unit_valuation_norm
      apply hsep p.1 p.2
      simpa using hp
    · rename_i hempty
      exfalso
      apply hempty
      exact ⟨(i, i'), by simp [hii']⟩

@[blueprint "lem:normalized-maximum-copy-bound"
  (statement := /-- Let $I$ be an admissible finite grouped goods instance, and let
  $\mu$ be its advertised copy lower bound. If $\mu>0$ and $\mu\le k_z$ for every
  item type $z$, then $\widetilde v_{\max}(\mathbf k)\le1/\sqrt\mu$. -/)
  (proof := /-- Write $\mu$ for the advertised bound from
  \cref{def:advertised-copy-lower-bound}. By
  \cref{def:maximum-copy-normalized-item-value, def:copy-weighted-normalized-value,
  def:copy-weighted-valuation-norm}, it suffices to fix a group $i$ and an item
  type $z$ and bound
  \[
    \frac{v_{i,z}}{\sqrt{\sum_w k_wv_{i,w}^2}}.
  \]
  Admissibility in \cref{def:goods-profile-assumptions} gives $v_{i,w}\ge0$
  for every $w$ and $S_i:=\sum_wv_{i,w}^2>0$. Since every square is
  nonnegative, $v_{i,z}^2\le S_i$. The pointwise copy-count hypothesis gives
  \[
    \mu S_i=\sum_w\mu v_{i,w}^2
      \le\sum_w k_wv_{i,w}^2=:W_i.
  \]
  Thus $W_i>0$, because $\mu>0$ and $S_i>0$. Using
  $(\sqrt\mu)^2=\mu$ and $(\sqrt{W_i})^2=W_i$, one obtains
  \[
    (v_{i,z}\sqrt\mu)^2
      =v_{i,z}^2\mu
      \le S_i\mu
      =\mu S_i
      \le W_i
      =(\sqrt{W_i})^2.
  \]
  Both $v_{i,z}\sqrt\mu$ and $\sqrt{W_i}$ are nonnegative, so the preceding
  squared inequality yields $v_{i,z}\sqrt\mu\le\sqrt{W_i}$. Dividing by the
  positive square roots of $W_i$ and $\mu$ gives
  $v_{i,z}/\sqrt{W_i}\le1/\sqrt\mu$. Taking the maximum over all $i$ and
  $z$ proves the claim. -/)
  (title := /-- Maximum normalized value under many copies -/)
  (latexEnv := "lemma")]
lemma normalized_maximum_copy_bound {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hmu : 0 < advertised_copy_lower_bound I)
    (hlower : ∀ z, advertised_copy_lower_bound I ≤ (I.copies z : ℝ)) :
    maximum_copy_normalized_item_value I ≤
      1 / Real.sqrt (advertised_copy_lower_bound I) := by
  classical
  rw [maximum_copy_normalized_item_value]
  apply Finset.sup'_le
  rintro ⟨i, z⟩ _
  simp only [copy_weighted_normalized_value, copy_weighted_valuation_norm]
  have hval : ∀ j w, 0 ≤ I.valuation j w := hprofile.2.2.2.1
  have hsum_pos : 0 < ∑ w, (I.valuation i w) ^ 2 :=
    Real.sqrt_pos.mp (hprofile.2.2.2.2.1 i)
  have hterm_le : (I.valuation i z) ^ 2 ≤ ∑ w, (I.valuation i w) ^ 2 := by
    have hz := Finset.single_le_sum
      (s := (Finset.univ : Finset ItemType))
      (f := fun w => (I.valuation i w) ^ 2)
      (fun w hw => sq_nonneg (I.valuation i w))
      (Finset.mem_univ z)
    exact hz
  have hweighted :
      advertised_copy_lower_bound I * (∑ w, (I.valuation i w) ^ 2) ≤
        ∑ w, (I.copies w : ℝ) * (I.valuation i w) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    exact mul_le_mul_of_nonneg_right (hlower w) (sq_nonneg (I.valuation i w))
  have hweighted_pos :
      0 < ∑ w, (I.copies w : ℝ) * (I.valuation i w) ^ 2 :=
    lt_of_lt_of_le (mul_pos hmu hsum_pos) hweighted
  have hsqrt_weighted_pos :
      0 < Real.sqrt (∑ w, (I.copies w : ℝ) * (I.valuation i w) ^ 2) :=
    Real.sqrt_pos.2 hweighted_pos
  have hsqrt_mu_pos : 0 < Real.sqrt (advertised_copy_lower_bound I) :=
    Real.sqrt_pos.2 hmu
  apply (div_le_div_iff₀ hsqrt_weighted_pos hsqrt_mu_pos).2
  simp only [one_mul]
  have hsquare :
      (I.valuation i z * Real.sqrt (advertised_copy_lower_bound I)) ^ 2 ≤
        ∑ w, (I.copies w : ℝ) * (I.valuation i w) ^ 2 := by
    calc
      (I.valuation i z * Real.sqrt (advertised_copy_lower_bound I)) ^ 2 =
          (I.valuation i z) ^ 2 * advertised_copy_lower_bound I := by
            rw [mul_pow, Real.sq_sqrt (le_of_lt hmu)]
      _ ≤ (∑ w, (I.valuation i w) ^ 2) * advertised_copy_lower_bound I :=
        mul_le_mul_of_nonneg_right hterm_le (le_of_lt hmu)
      _ = advertised_copy_lower_bound I * (∑ w, (I.valuation i w) ^ 2) := by
        rw [mul_comm]
      _ ≤ ∑ w, (I.copies w : ℝ) * (I.valuation i w) ^ 2 := hweighted
  apply (sq_le_sq₀
    (mul_nonneg (hval i z) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)).mp
  simpa [Real.sq_sqrt (le_of_lt hweighted_pos)] using hsquare

@[blueprint "lem:advertised-numeric-comparison"
  (statement := /-- Let $I$ be an admissible goods instance with finite group and item-type sets and strictly positive copy counts. Write $n$ for the number of agents, $C$ for the rounding complexity, and $\mu$ for the advertised copy lower bound. If every copy count lies in the half-open window $[\mu,\mu+n)$, then
  \[
  4nC\le \mu\,
  \min_{i\ne i'}\lVert\widetilde v_i(\mathbf k)-
  \widetilde v_{i'}(\mathbf k)\rVert_2^2.
  \] -/)
  (proof := /-- Put $s=\min_{i\ne i'}\lVert\widetilde v_i-\widetilde v_{i'}\rVert_2^2$ and $b=\sqrt{s}$. By \cref{def:goods-profile-assumptions, def:unit-normalized-value, def:unit-valuation-norm}, every unit normalized valuation vector has squared norm one. Thus $(x-y)^2\le 2x^2+2y^2$, summed over item types, shows from \cref{def:unit-separation-squared, def:minimum-unit-separation-squared} that $0<s\le4$, and hence $0<b\le2$. The distinct groups supplied by admissibility and the positive group sizes give $d\ge2$ and $n>0$ through \cref{def:number-of-groups, def:number-of-agents}.

  Let $A$ be the advertised copy complexity. The definitions in \cref{def:advertised-copy-complexity, def:rounding-complexity} give $A=C+d$ and $A\ge d^2\ge4$. By \cref{lem:advertised-copy-bound-positive}, $\mu>0$, and \cref{def:advertised-copy-lower-bound} gives
  \[
    \mu b^2=4nA.
  \]
  Since $b^2\le2b$, $b+1\le3$, and $A\ge4$, one has
  $n(b+1)\le4nA=\mu b^2\le2\mu b$. Therefore
  $n(b+1)/(2b)\le\mu$, so \cref{lem:scalar-square-root-lower-bound} yields
  \[
    \mu b^2-nb(b+1)\le
    \mu\left(\sqrt{\frac{\mu}{\mu+n}}b-
      \left(1-\sqrt{\frac{\mu}{\mu+n}}\right)\right)^2.
  \]
  The same inequality $n(b+1)\le2\mu b$ implies $n\le2\mu$. The identity
  \[
    \frac{\mu}{\mu+n}-\left(1-\frac{n}{2\mu}\right)^2
    =\frac{n^2(3\mu-n)}{4\mu^2(\mu+n)}\ge0
  \]
  shows that the expression inside the preceding square is nonnegative. The strict copy-count upper bound implies the weak bound $k_z\le\mu+n$, so \cref{lem:minimum-copy-distance-lower-bound} bounds this expression above by $\sqrt{\delta(\mathbf k)^2}$. The definitions in \cref{def:copy-weighted-separation-squared, def:minimum-copy-weighted-separation-squared} give $\delta(\mathbf k)^2\ge0$; squaring and multiplying by $\mu>0$ therefore bounds the preceding right-hand side by $\mu\delta(\mathbf k)^2$.

  Finally, $b\le2$ and $d\ge2$ imply $b(b+1)\le6\le4d$. Using $A=C+d$ and $\mu b^2=4nA$ gives
  \[
    4nC\le \mu b^2-nb(b+1)\le\mu\delta(\mathbf k)^2,
  \]
  as required. -/)
  (title := /-- Numerical comparison from the advertised bound -/)
  (latexEnv := "lemma")]
lemma advertised_numeric_comparison {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (hlower : ∀ z, advertised_copy_lower_bound I ≤ (I.copies z : ℝ))
    (hupper : ∀ z, (I.copies z : ℝ) <
      advertised_copy_lower_bound I + number_of_agents I) :
    ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) ≤
      advertised_copy_lower_bound I * minimum_copy_weighted_separation_squared I := by
  classical
  have hprofile' := hprofile
  rcases hprofile' with
    ⟨hgroup_pos, hsmall, hgroup_large, hvaluation_nonnegative, hnorm_pos,
      hpairs_exist, hseparation_pos⟩
  obtain ⟨i, i', hii'⟩ := hpairs_exist
  have hpairs : ((Finset.univ.product Finset.univ).filter
      (fun p : Group × Group => p.1 ≠ p.2)).Nonempty := by
    exact ⟨(i, i'), by simp [hii']⟩
  have hunit_norm (j : Group) :
      ∑ z, (unit_normalized_value I j z) ^ 2 = 1 := by
    have hsum_pos : 0 < ∑ z, (I.valuation j z) ^ 2 :=
      Real.sqrt_pos.mp (hnorm_pos j)
    simp only [unit_normalized_value, unit_valuation_norm]
    simp_rw [div_pow]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, Real.sq_sqrt hsum_pos.le,
      mul_inv_cancel₀ hsum_pos.ne']
  have hseparation_le (j j' : Group) : unit_separation_squared I j j' ≤ 4 := by
    unfold unit_separation_squared
    calc
      ∑ z, (unit_normalized_value I j z -
          unit_normalized_value I j' z) ^ 2 ≤
          ∑ z, (2 * (unit_normalized_value I j z) ^ 2 +
            2 * (unit_normalized_value I j' z) ^ 2) := by
        apply Finset.sum_le_sum
        intro z hz
        nlinarith [sq_nonneg (unit_normalized_value I j z +
          unit_normalized_value I j' z)]
      _ = 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hunit_norm j, hunit_norm j']
        norm_num
  have hminimum_pos : 0 < minimum_unit_separation_squared I := by
    simp only [minimum_unit_separation_squared, dif_pos hpairs]
    obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_inf' hpairs
      (fun p => unit_separation_squared I p.1 p.2)
    rw [heq]
    apply hseparation_pos
    simpa using hp
  have hminimum_le : minimum_unit_separation_squared I ≤ 4 := by
    simp only [minimum_unit_separation_squared, dif_pos hpairs]
    calc
      ((Finset.univ.product Finset.univ).filter
          (fun p : Group × Group => p.1 ≠ p.2)).inf' hpairs
          (fun p => unit_separation_squared I p.1 p.2) ≤
          unit_separation_squared I i i' := by
        exact Finset.inf'_le
          (s := (Finset.univ.product Finset.univ).filter
            (fun p : Group × Group => p.1 ≠ p.2))
          (b := (i, i'))
          (fun p : Group × Group => unit_separation_squared I p.1 p.2)
          (by simp [hii'])
      _ ≤ 4 := hseparation_le i i'
  let b : ℝ := Real.sqrt (minimum_unit_separation_squared I)
  have hbpos : 0 < b := by
    exact Real.sqrt_pos.2 hminimum_pos
  have hbsquare : b ^ 2 = minimum_unit_separation_squared I := by
    exact Real.sq_sqrt hminimum_pos.le
  have hble : b ≤ 2 := by
    nlinarith [sq_nonneg (b - 2)]
  have hn_nat : 0 < number_of_agents I := by
    unfold number_of_agents
    exact Finset.sum_pos (fun j _ => hgroup_pos j) ⟨i, Finset.mem_univ i⟩
  have hn : 0 < (number_of_agents I : ℝ) := by
    exact_mod_cast hn_nat
  have hd_nat : 2 ≤ number_of_groups I := by
    unfold number_of_groups
    exact Fintype.one_lt_card_iff.mpr ⟨i, i', hii'⟩
  have hd : (2 : ℝ) ≤ number_of_groups I := by
    exact_mod_cast hd_nat
  have hcomplexity_eq :
      advertised_copy_complexity I =
        rounding_complexity I + number_of_groups I := by
    have hsquare : number_of_groups I ^ 2 =
        number_of_groups I * (number_of_groups I - 1) + number_of_groups I := by
      rw [pow_two]
      calc
        number_of_groups I * number_of_groups I =
            number_of_groups I * ((number_of_groups I - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ number_of_groups I)]
        _ = number_of_groups I * (number_of_groups I - 1) +
            number_of_groups I := by simp [Nat.mul_add]
    unfold advertised_copy_complexity rounding_complexity
    rw [hsquare]
    omega
  have hadvertised_ge_nat : 4 ≤ advertised_copy_complexity I := by
    have hsquare : 4 ≤ number_of_groups I ^ 2 := by
      nlinarith
    unfold advertised_copy_complexity
    omega
  have hadvertised_ge : (4 : ℝ) ≤ advertised_copy_complexity I := by
    exact_mod_cast hadvertised_ge_nat
  have hmu : 0 < advertised_copy_lower_bound I :=
    advertised_copy_bound_positive I hprofile
  have hmu_identity :
      advertised_copy_lower_bound I * b ^ 2 =
        4 * (number_of_agents I : ℝ) * (advertised_copy_complexity I : ℝ) := by
    rw [hbsquare]
    unfold advertised_copy_lower_bound
    field_simp [hminimum_pos.ne']
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hbsquare_le : b ^ 2 ≤ 2 * b := by
    nlinarith
  have hlarge :
      (number_of_agents I : ℝ) * (b + 1) / (2 * b) ≤
        advertised_copy_lower_bound I := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * b)).2
    have hfront :
        (number_of_agents I : ℝ) * (b + 1) ≤
          4 * (number_of_agents I : ℝ) * (advertised_copy_complexity I : ℝ) := by
      nlinarith
    calc
      (number_of_agents I : ℝ) * (b + 1) ≤
          4 * (number_of_agents I : ℝ) * (advertised_copy_complexity I : ℝ) :=
        hfront
      _ = advertised_copy_lower_bound I * b ^ 2 := hmu_identity.symm
      _ ≤ advertised_copy_lower_bound I * (2 * b) :=
        mul_le_mul_of_nonneg_left hbsquare_le hmu.le
  have hscalar := scalar_square_root_lower_bound
    (number_of_agents I : ℝ) b (advertised_copy_lower_bound I)
    (by positivity) hbpos.le hmu.le hlarge
  have hupper' : ∀ z, (I.copies z : ℝ) ≤
      advertised_copy_lower_bound I + (number_of_agents I : ℝ) :=
    fun z => (hupper z).le
  have hdistance := minimum_copy_distance_lower_bound I hprofile
    (advertised_copy_lower_bound I)
    (advertised_copy_lower_bound I + (number_of_agents I : ℝ)) hmu
    (le_add_of_nonneg_right hn.le) hlower hupper'
  have hcross :
      (number_of_agents I : ℝ) * (b + 1) ≤
        advertised_copy_lower_bound I * (2 * b) :=
    (div_le_iff₀ (by positivity : 0 < 2 * b)).mp hlarge
  have hbaddpos : 0 < b + 1 := by positivity
  have hcross' :
      (number_of_agents I : ℝ) * (b + 1) ≤
        (2 * advertised_copy_lower_bound I) * (b + 1) := by
    nlinarith
  have hatwo : (number_of_agents I : ℝ) ≤
      2 * advertised_copy_lower_bound I :=
    (mul_le_mul_iff_of_pos_right hbaddpos).mp hcross'
  have hthree : 0 ≤ 3 * advertised_copy_lower_bound I -
      (number_of_agents I : ℝ) := by
    nlinarith
  have hquotle :
      (number_of_agents I : ℝ) / (2 * advertised_copy_lower_bound I) ≤ 1 := by
    apply (div_le_iff₀
      (by positivity : 0 < 2 * advertised_copy_lower_bound I)).mpr
    nlinarith
  have hsqrt_lower :
      1 - (number_of_agents I : ℝ) / (2 * advertised_copy_lower_bound I) ≤
        Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) := by
    apply (Real.le_sqrt (by nlinarith [hquotle]) (by positivity)).mpr
    have hid :
        advertised_copy_lower_bound I /
            (advertised_copy_lower_bound I + (number_of_agents I : ℝ)) -
          (1 - (number_of_agents I : ℝ) /
            (2 * advertised_copy_lower_bound I)) ^ 2 =
          (number_of_agents I : ℝ) ^ 2 *
              (3 * advertised_copy_lower_bound I - (number_of_agents I : ℝ)) /
            (4 * advertised_copy_lower_bound I ^ 2 *
              (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) := by
      field_simp [hmu.ne'] <;> ring
    have hrem : 0 ≤
        (number_of_agents I : ℝ) ^ 2 *
            (3 * advertised_copy_lower_bound I - (number_of_agents I : ℝ)) /
          (4 * advertised_copy_lower_bound I ^ 2 *
            (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) := by
      positivity
    nlinarith
  have hbase : 0 ≤ b -
      (number_of_agents I : ℝ) * (b + 1) /
        (2 * advertised_copy_lower_bound I) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀
      (by positivity : 0 < 2 * advertised_copy_lower_bound I)).mpr
    nlinarith
  have hinner_nonneg : 0 ≤
      Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) * b -
        (1 - Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ)))) := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt_lower hbaddpos.le
    calc
      0 ≤ b - (number_of_agents I : ℝ) * (b + 1) /
          (2 * advertised_copy_lower_bound I) := hbase
      _ = (b + 1) *
          (1 - (number_of_agents I : ℝ) /
            (2 * advertised_copy_lower_bound I)) - 1 := by ring
      _ ≤ (b + 1) * Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) - 1 :=
        sub_le_sub_right hmul 1
      _ = Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) * b -
        (1 - Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ)))) := by ring
  have hcopy_nonneg : 0 ≤ minimum_copy_weighted_separation_squared I := by
    simp only [minimum_copy_weighted_separation_squared, dif_pos hpairs]
    obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_inf' hpairs
      (fun p => copy_weighted_separation_squared I p.1 p.2)
    rw [heq]
    unfold copy_weighted_separation_squared
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hdistance' :
      Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) * b -
        (1 - Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ)))) ≤
      Real.sqrt (minimum_copy_weighted_separation_squared I) := by
    simpa [b] using hdistance
  have hsquare_distance :
      (Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) * b -
        (1 - Real.sqrt (advertised_copy_lower_bound I /
          (advertised_copy_lower_bound I + (number_of_agents I : ℝ))))) ^ 2 ≤
        minimum_copy_weighted_separation_squared I := by
    have hmul := mul_self_le_mul_self hinner_nonneg hdistance'
    nlinarith [Real.sq_sqrt hcopy_nonneg]
  have hreserve :
      (number_of_agents I : ℝ) * b * (b + 1) ≤
        4 * (number_of_agents I : ℝ) * (number_of_groups I : ℝ) := by
    have hbb : b * (b + 1) ≤ 6 := by nlinarith
    have hbd : b * (b + 1) ≤ 4 * (number_of_groups I : ℝ) := by
      nlinarith
    nlinarith
  have hleft :
      ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) ≤
        b ^ 2 * advertised_copy_lower_bound I -
          (number_of_agents I : ℝ) * b * (b + 1) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hcomplexity_eq' : (advertised_copy_complexity I : ℝ) =
        (rounding_complexity I : ℝ) + (number_of_groups I : ℝ) := by
      exact_mod_cast hcomplexity_eq
    nlinarith [hmu_identity]
  calc
    ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) ≤
        b ^ 2 * advertised_copy_lower_bound I -
          (number_of_agents I : ℝ) * b * (b + 1) := hleft
    _ ≤ advertised_copy_lower_bound I *
        (Real.sqrt (advertised_copy_lower_bound I /
            (advertised_copy_lower_bound I + (number_of_agents I : ℝ))) * b -
          (1 - Real.sqrt (advertised_copy_lower_bound I /
            (advertised_copy_lower_bound I + (number_of_agents I : ℝ))))) ^ 2 :=
      hscalar
    _ ≤ advertised_copy_lower_bound I *
        minimum_copy_weighted_separation_squared I :=
      mul_le_mul_of_nonneg_left hsquare_distance hmu.le

@[blueprint "lem:normalized-sufficient-bound-from-numeric-comparison"
  (statement := /-- Let $I$ be an admissible finite goods instance. If $\mu>0$, $\widetilde v_{\max}(\mathbf k)\le1/\sqrt\mu$, and $4nC\le\mu\delta(\mathbf k)^2$, then
  $\widetilde v_{\max}(\mathbf k)\le\sqrt{\delta(\mathbf k)^2/(4nC)}$. -/)
  (proof := /-- By \cref{def:goods-profile-assumptions}, every group has positive size and two distinct groups exist. Consequently, \cref{def:number-of-agents, def:number-of-groups} give $n>0$ and $d\ge2$. The summand $d(d-1)$ in \cref{def:rounding-complexity} is therefore positive, so $C>0$ and hence $4nC>0$. Since $\mu>0$ and $4nC\le\mu\delta(\mathbf k)^2$, it also follows that $\delta(\mathbf k)^2>0$. It remains, by transitivity with the assumed bound on $\widetilde v_{\max}(\mathbf k)$, to prove
  $1/\sqrt\mu\le\sqrt{\delta(\mathbf k)^2/(4nC)}$. Both sides are nonnegative, and squaring this inequality reduces it to $1/\mu\le\delta(\mathbf k)^2/(4nC)$. Cross-multiplication by the positive quantities $\mu$ and $4nC$ reduces the latter inequality precisely to the assumed numerical comparison. -/)
  (title := /-- Conversion to the sufficient normalized-value bound -/)
  (latexEnv := "lemma")]
lemma normalized_sufficient_bound_from_numeric_comparison {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hmu : 0 < advertised_copy_lower_bound I)
    (hmax : maximum_copy_normalized_item_value I ≤
      1 / Real.sqrt (advertised_copy_lower_bound I))
    (hnumeric : ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) ≤
      advertised_copy_lower_bound I * minimum_copy_weighted_separation_squared I) :
    maximum_copy_normalized_item_value I ≤
      Real.sqrt (minimum_copy_weighted_separation_squared I /
        ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ)) := by
  have hn : 0 < number_of_agents I := by
    unfold number_of_agents
    exact Finset.sum_pos (fun i _ => hprofile.1 i) ⟨I.smallestGroup, Finset.mem_univ _⟩
  have hd : 1 < number_of_groups I := by
    unfold number_of_groups
    exact Fintype.one_lt_card_iff.mpr hprofile.2.2.2.2.2.1
  have hgroup_term :
      0 < number_of_groups I * (number_of_groups I - 1) := by
    exact Nat.mul_pos (by omega) (Nat.sub_pos_iff_lt.mpr hd)
  have hcomplexity : 0 < rounding_complexity I := by
    unfold rounding_complexity
    omega
  have hden_nat :
      0 < 4 * number_of_agents I * rounding_complexity I := by
    positivity
  have hden :
      0 < ((4 * number_of_agents I * rounding_complexity I : ℕ) : ℝ) := by
    exact_mod_cast hden_nat
  have hseparation : 0 < minimum_copy_weighted_separation_squared I := by
    exact pos_of_mul_pos_right (hden.trans_le hnumeric) hmu.le
  apply hmax.trans
  refine (Real.le_sqrt (by positivity) (by positivity)).2 ?_
  rw [div_pow, one_pow, Real.sq_sqrt hmu.le]
  exact (div_le_div_iff₀ hmu hden).2 (by simpa [mul_comm] using hnumeric)

@[blueprint "lem:bounded-copy-instance-admits-envy-free-allocation"
  (statement := /-- Let $I$ be a fair-goods instance over finite group and
  item-type spaces, and suppose that $I$ satisfies the goods-profile assumptions
  in \cref{def:goods-profile-assumptions}. Write $g$ for the gcd of the group
  sizes, $\mu$ for the advertised copy lower bound, and $n$ for the total number
  of agents. If, for every item type $z$, the copy count $k_z$ is positive,
  divisible by $g$, and satisfies $\mu\le k_z<\mu+n$, then $I$ admits a complete
  integral envy-free allocation in which all agents in each group receive the
  same bundle. -/)
  (proof := /-- For every item type $z$,
  \cref{lem:advertised-bound-at-least-threshold} gives $\theta\le\mu$, and the
  lower window hypothesis gives $\mu\le k_z$; hence $\theta\le k_z$.
  By \cref{lem:advertised-copy-bound-positive}, one has $\mu>0$, so the lower
  window hypothesis and \cref{lem:normalized-maximum-copy-bound} imply
  $\widetilde v_{\max}(\mathbf k)\le1/\sqrt\mu$. Admissibility, positivity of
  the copy counts, and both window inequalities allow
  \cref{lem:advertised-numeric-comparison} to yield
  $4nC\le\mu\delta(\mathbf k)^2$. Therefore
  \cref{lem:normalized-sufficient-bound-from-numeric-comparison} gives
  \[
    \widetilde v_{\max}(\mathbf k)\le
    \sqrt{\frac{\delta(\mathbf k)^2}{4nC}}.
  \]
  Finally, apply \cref{lem:envy-free-sufficient-condition} using admissibility,
  positivity, the threshold inequalities, gcd divisibility, and this normalized
  value bound. -/)
  (title := /-- Envy-freeness in the bounded-copy window -/)
  (latexEnv := "lemma")]
lemma bounded_copy_instance_admits_envy_free_allocation {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (hdiv : ∀ z, group_size_gcd I ∣ I.copies z)
    (hlower : ∀ z, advertised_copy_lower_bound I ≤ (I.copies z : ℝ))
    (hupper : ∀ z, (I.copies z : ℝ) <
      advertised_copy_lower_bound I + number_of_agents I) :
    admits_envy_free_allocation I := by
  apply envy_free_sufficient_condition I hprofile hpositive
  · intro z
    exact_mod_cast
      (advertised_bound_at_least_threshold I hprofile).trans (hlower z)
  · exact hdiv
  · apply normalized_sufficient_bound_from_numeric_comparison I hprofile
    · exact advertised_copy_bound_positive I hprofile
    · exact normalized_maximum_copy_bound I hprofile
        (advertised_copy_bound_positive I hprofile) hlower
    · exact advertised_numeric_comparison I hprofile hpositive hlower hupper

@[blueprint "thm:existence-of-envy-free-goods-allocation"
  (statement := /-- Let the groups and the types of indivisible goods be indexed by nonempty finite sets. For every group $i$, let its size $n_i$ be positive, and let distinguished groups of sizes $n_1$ and $n_d$ attain, respectively, the minimum and maximum group sizes. Every agent in group $i$ has the same additive valuation $v_i$, with $v_i(z)\ge 0$ for every type $z$. Assume that there are at least two groups, that every unit-copy valuation vector $v_i$ has positive Euclidean norm, and that the normalized unit-copy valuation vectors of every two distinct groups have positive Euclidean distance. Let $n=\sum_i n_i$, let $d$ and $t$ be the numbers of groups and types, let $g=\gcd_i n_i$, and set $\theta=g(n_1/g-1)(n_d/g-1)$. If every type $z$ has a positive number $k_z$ of copies satisfying
  \[
  k_z\ge
  \frac{4n\bigl(d^2+t(\theta+n+n_d-d-1)\bigr)}
  {\min_{i\ne i'}\lVert\widetilde v_i-
  \widetilde v_{i'}\rVert_2^2}
  \quad\text{and}\quad g\mid k_z,
  \]
  where the minimum is over all ordered pairs of distinct groups, then there exists a complete integral envy-free allocation in which all agents of the same group receive the same bundle. -/)
  (proof := /-- Apply \cref{lem:copy-window-reduction} with the advertised lower bound $\mu$. It supplies a positive residual copy vector $r$, divisible by $g$, whose coordinates lie in $[\mu,\mu+n)$, and integers $q_z\ge0$ satisfying $k_z=r_z+q_zn$. The valuation profile, group sizes, gcd, threshold, and advertised bound are unchanged when only the copy vector is replaced. Hence \cref{lem:bounded-copy-instance-admits-envy-free-allocation} gives a complete envy-free allocation for the residual instance. The lifting implication furnished by the reduction adds the $q_z$ removed uniform rounds and yields the required allocation of the original instance. -/)
  (title := /-- Existence of an envy-free allocation for sufficiently many goods copies -/)
  (latexEnv := "theorem")]
theorem existence_of_envy_free_goods_allocation {Group ItemType : Type*}
    [Fintype Group] [Fintype ItemType] (I : fair_goods_instance Group ItemType)
    (hprofile : goods_profile_assumptions I)
    (hpositive : ∀ z, 0 < I.copies z)
    (hbound : ∀ z, advertised_copy_lower_bound I ≤ (I.copies z : ℝ))
    (hdiv : ∀ z, group_size_gcd I ∣ I.copies z) :
    admits_envy_free_allocation I := by
  obtain ⟨r, _, hrpos, hrlow, hrupper, hrdiv, _, hlift⟩ :=
    copy_window_reduction I hprofile hpositive hbound hdiv
  apply hlift
  exact bounded_copy_instance_admits_envy_free_allocation
    (instance_with_copies I r) hprofile hrpos hrdiv hrlow hrupper

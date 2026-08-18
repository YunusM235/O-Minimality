import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.DenselyOrdered
import TameGeometry.Definability
import TameGeometry.Topology

/-!
# O-Minimality and definable completeness

we define O-Minimality and definable completeness
and we show some basic properties.

-/

namespace TameGeometry

open FirstOrder FirstOrder.Language

variable {M : Type*} [LinearOrder M]

inductive IsBasic : Set M → Prop
  | point (p : M) : IsBasic {p}
  | Ioo (a b : M) (h : a < b) : IsBasic (Set.Ioo a b)
  | Ioi (a : M) : IsBasic (Set.Ioi a)
  | Iio (b : M) : IsBasic (Set.Iio b)
  | Iii : IsBasic (Set.univ)

/-- A set is tame if it is a finite union of basic sets -/
def IsTame (s : Set M) : Prop :=
  ∃ (A : Finset (Set M)), (∀ a ∈ A, IsBasic a) ∧ s = ⋃ a ∈ A, a

/-- A structure is O-Minimal if every definable set is a finite union of points and intervals -/
class OMinimal (L : Language) (M : Type*) [L.IsOrdered] [L.Structure M] [M ⊨ L.dlo]
  [LinearOrder M] [L.OrderedStructure M] : Prop where
  is_ominimal : ∀ {s : Set M}, Set.univ.Definable₁ L s → IsTame s

/-- A structure is definably complete if
every non-empty bounded definable set has an infimum and supremum in the structure -/
class DefinablyComplete (L : Language) (M : Type*) [L.IsOrdered] [L.Structure M] [M ⊨ L.dlo]
  [LinearOrder M] [L.OrderedStructure M] : Prop where
  glb : ∀ (s : Set M), s.Nonempty → Set.univ.Definable₁ L s → BddBelow s → ∃ a, IsGLB s a
  lub : ∀ (s : Set M), s.Nonempty → Set.univ.Definable₁ L s → BddAbove s → ∃ b, IsLUB s b

lemma tame_induction (P : Set M → Prop) (h0 : P ∅)
    (hi : ∀ (s b : Set M), IsTame s → IsBasic b → P s → P (s ∪ b)) :
    ∀ s, IsTame s → P s := by
  intro s ⟨A, h1, h2⟩
  subst h2
  revert h1
  induction A using Finset.induction with
  | empty => simp [h0]
  | insert a A ha ih =>
    intro h1
    rw [Finset.set_biUnion_insert, Set.union_comm]
    have h2 : IsTame (⋃ x ∈ A, x) := ⟨A, fun a ha ↦ h1 a (Finset.mem_insert_of_mem ha), rfl⟩
    have h3 : P (⋃ x ∈ A, x) := ih (fun a ha ↦ h1 a (Finset.mem_insert_of_mem ha))
    exact hi (⋃ x ∈ A, x) a h2 (h1 a (Finset.mem_insert_self a A)) h3

/-- basic sets that are bounded below are a point, an open interval or a left-open interval -/
lemma bdd_below_basic [NoMinOrder M] (s : Set M) (h1 : IsBasic s) (h2 : BddBelow s) :
    (∃ p, s = {p}) ∨ (∃ a b, a < b ∧ s = Set.Ioo a b) ∨ (∃ a, s = Set.Ioi a) := by
  cases h1 with
  | point p => left; use p
  | Ioo a b => right; left; use a, b
  | Ioi a => right; right; use a
  | Iio b => exact absurd h2 (not_bddBelow_Iio b)
  | Iii => exact absurd h2 not_bddBelow_univ

/-- basic sets that are bounded above are a point, an open interval or a right-open interval -/
lemma bdd_above_basic [NoMaxOrder M] (s : Set M) (h1 : IsBasic s) (h2 : BddAbove s) :
    (∃ p, s = {p}) ∨ (∃ a b, a < b ∧ s = Set.Ioo a b) ∨ (∃ b, s = Set.Iio b) := by
  cases h1 with
  | point p => left; use p
  | Ioo a b => right; left; use a, b
  | Ioi a => by_contra; exact absurd h2 (not_bddAbove_Ioi a)
  | Iio b => right; right; use b
  | Iii => by_contra; exact absurd h2 not_bddAbove_univ

/-- basic sets which are bounded below have an infimum -/
lemma bdd_below_basic_glb [NoMinOrder M] [DenselyOrdered M]
    (s : Set M) (h1 : IsBasic s) (h2 : BddBelow s) :
    ∃ x, IsGLB s x := by
  obtain h3 | h4 | h5 := bdd_below_basic s h1 h2
  · obtain ⟨p, hp⟩ := h3
    use p
    rw [hp]
    exact isGLB_singleton
  · obtain ⟨a, b, hab⟩ := h4
    use a
    rw [hab.right]
    exact isGLB_Ioo hab.left
  · obtain ⟨a, ha⟩ := h5
    use a
    rw [ha]
    exact isGLB_Ioi

/-- basic sets which are bounded above have a supremum -/
lemma bdd_above_basic_lub [NoMaxOrder M] [DenselyOrdered M]
    (s : Set M) (h1 : IsBasic s) (h2 : BddAbove s) :
    ∃ x, IsLUB s x := by
  obtain h3 | h4 | h5 := bdd_above_basic s h1 h2
  · obtain ⟨p, hp⟩ := h3
    use p
    rw [hp]
    exact isLUB_singleton
  · obtain ⟨a, b, hab⟩ := h4
    use b
    rw [hab.right]
    exact isLUB_Ioo hab.left
  · obtain ⟨b, hb⟩ := h5
    use b
    rw [hb]
    exact isLUB_Iio

/-- Bounded below tame sets have an infimum -/
lemma has_glb [NoMinOrder M] [DenselyOrdered M] :
    ∀ (s : Set M), IsTame s → s.Nonempty → BddBelow s → ∃ x, IsGLB s x := by
  apply tame_induction
  · simp
  · intro s b h1 h2 h3 h4 h5
    by_cases h : s.Nonempty
    · obtain ⟨xs, hxs⟩ := (h3 h (h5.mono Set.subset_union_left))
      obtain ⟨xb, hxb⟩ := bdd_below_basic_glb b h2 (h5.mono Set.subset_union_right)
      use (min xs xb)
      exact IsGLB.union hxs hxb
    · push Not at h
      subst h
      rw [Set.empty_union] at *
      exact bdd_below_basic_glb b h2 h5

/-- Bounded above tame sets have a supremum -/
lemma has_lub [NoMaxOrder M] [DenselyOrdered M] :
    ∀ (s : Set M), IsTame s → s.Nonempty → BddAbove s → ∃ x, IsLUB s x := by
  apply tame_induction
  · simp
  · intro s b h1 h2 h3 h4 h5
    by_cases h : s.Nonempty
    · obtain ⟨xs, hxs⟩ := (h3 h (h5.mono Set.subset_union_left))
      obtain ⟨xb, hxb⟩ := bdd_above_basic_lub b h2 (h5.mono Set.subset_union_right)
      use (max xs xb)
      exact IsLUB.union hxs hxb
    · push Not at h
      subst h
      rw [Set.empty_union] at *
      exact bdd_above_basic_lub b h2 h5

/-- For a basic set $s$ and $a ∈ M$ there is some $b ∈ M$ such that
  $(a,b)$ is either contained in $s$ or disjoint with $s$ -/
lemma isBasic_right_interval [NoMaxOrder M]
    {s : Set M} (hs : IsBasic s) (a : M) :
    (∃ b > a, Set.Ioo a b ⊆ s) ∨ (∃ b > a, Disjoint (Set.Ioo a b) s) := by
  cases hs with
  | Ioo c d hcd =>
    by_cases h : d ≤ a
    · obtain ⟨b, hb⟩ := exists_gt a
      grind
    · push Not at h
      by_cases h' : a < c <;> grind
  | Iii =>
    obtain ⟨b, hb⟩ := exists_gt a
    grind
  | Ioi c | Iio c | point c =>
    by_cases h : c ≤ a
    · obtain ⟨b, hb⟩ := exists_gt a
      grind
    · push Not at h
      grind

/-- For a tame set $s$ and $a ∈ M$ there is some $b ∈ M$ such that
  $(a,b)$ is either contained in $s$ or disjoint with $s$ -/
lemma isTame_right_interval [NoMaxOrder M]
    {s : Set M} (hs : IsTame s) (a : M) :
    (∃ b > a, Set.Ioo a b ⊆ s) ∨ (∃ b > a, Disjoint (Set.Ioo a b) s) := by
  revert s
  apply tame_induction
  · right
    obtain ⟨b, hb⟩ := exists_gt a
    grind
  · intro s s' hs hs' h
    obtain (ha | hb) := h
    · grind
    · obtain (ha' | hb') := isBasic_right_interval hs' a
      <;> grind

/-- An infinite basic set contains a non-empty open interval -/
lemma isBasic_infinite_has_ioo [NoMaxOrder M] [NoMinOrder M]
    {s : Set M} (ht : IsBasic s) (hi : s.Infinite) :
    ∃ a b, a < b ∧ Set.Ioo a b ⊆ s := by
  cases ht with
    | point p =>
      have := Set.finite_singleton p
      contradiction
    | Ioo c d hcd => grind
    | Ioi c =>
      obtain ⟨b, hb⟩ := exists_gt c
      refine ⟨c, b, ⟨hb, Set.Ioo_subset_Ioi_self⟩⟩
    | Iio c =>
      obtain ⟨a, ha⟩ := exists_lt c
      exact ⟨a, c, ha, Set.Ioo_subset_Iio_self⟩
    | Iii =>
      obtain ⟨a, ha⟩ := hi.nonempty
      obtain ⟨b, hb⟩ := exists_gt a
      exact ⟨a, b, ⟨hb, by exact Set.subset_univ (Set.Ioo a b)⟩⟩

/-- An infinite tame set contains a non-empty open interval -/
lemma isTame_infinite_has_ioo [NoMaxOrder M] [NoMinOrder M]
    {s : Set M} (h1s : IsTame s) (h2s : s.Infinite) :
    ∃ a b, a < b ∧ Set.Ioo a b ⊆ s := by
  obtain ⟨A, h1A, h2A⟩ := h1s
  have : ∃ w ∈ A, w.Infinite := by
    by_contra!
    have : s.Finite := by
      rw [h2A]
      apply Finite.Set.finite_biUnion (A : Set (Set M)) id
      intro i hi
      exact this i hi
    contradiction
  obtain ⟨w, hw1, hw2⟩ := this
  obtain ⟨a, b, h1, h2⟩ := isBasic_infinite_has_ioo (h1A w hw1) hw2
  have : w ⊆ s := by
    rw [h2A]
    apply Set.subset_iUnion₂_of_subset w
    · trivial
    · exact hw1
  exact ⟨a, b, h1, by grind⟩

variable (L : Language) [L.IsOrdered] [L.Structure M] [M ⊨ L.dlo] [L.OrderedStructure M]

/-- O-Minimal structures are definably complete -/
instance [OMinimal L M] [NoMaxOrder M] [NoMinOrder M] [DenselyOrdered M] :
  DefinablyComplete L M where
  glb s h1 h2 h3 := has_glb (M:=M) s (OMinimal.is_ominimal h2) h1 h3
  lub s h1 h2 h3 := has_lub (M:=M) s (OMinimal.is_ominimal h2) h1 h3

lemma isBasic_open_or_singleton [TopologicalSpace M] [OrderTopology M]
    {s : Set M} (h : IsBasic s) :
    IsOpen s ∨ ∃ p, s = {p} := by
  cases h with
    | point p =>
      right
      use p
    | _ =>
      left
      simp [isOpen_Ioo, isOpen_Iio, isOpen_Ioi]

variable {L}

/-- Every set definable in an O-minimal structure has a finite frontier -/
lemma omin_bd_fin [OMinimal L M] [TopologicalSpace M] [OrderTopology M]
    [NoMaxOrder M] [NoMinOrder M] [DenselyOrdered M]
    (s : Set M) (h : Set.univ.Definable₁ L s) : (frontier s).Finite := by
  obtain ⟨A, ⟨h1,h2⟩⟩ := OMinimal.is_ominimal h
  rw [h2]
  apply Set.Finite.subset (ht := frontier_union A)
  apply Finite.Set.finite_biUnion
  intro i hi
  specialize h1 i hi
  cases h1 with
    | Ioo a b h => simp [Set.finite_coe_iff, h]
    | _ => simp [Set.finite_coe_iff, frontier]

/-- Let $Y_1,…,Y_n$ be a definable covering of some open interval $(a,b)$.
For all $c ∈ (a,b)$ there is some $d ∈ (a,b)$ and $i$ such that $(c,d) ⊆ Y_i$.
-/
lemma ioo_def_covering [OMinimal L M] [DenselyOrdered M] [NoMaxOrder M]
    {n : ℕ} {a b c : M} (Y : Fin n → (Set M)) (h1Y : Set.Ioo a b ⊆ ⋃ i, Y i)
    (h2Y : ∀ i, Set.univ.Definable₁ L (Y i)) (hc : c ∈ Set.Ioo a b) :
    ∃ i, ∃ d ∈ Set.Ioo a b, c < d ∧ Set.Ioo c d ⊆ Y i := by
  by_cases h1 : ∃ i, ∃ d > c, Set.Ioo c d ⊆ Y i
  · obtain ⟨i, d, hd1, hd2⟩ := h1
    obtain ⟨x, h1x, h2x⟩ := exists_between (lt_min hd1 hc.2)
    use i, x
    grind
  · rw [not_exists] at h1
    have h2 := fun i ↦
      Or.resolve_left (isTame_right_interval (OMinimal.is_ominimal (h2Y i)) c) (h1 i)
    choose d hd using h2
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp (h1Y hc)
    have h3 : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
    obtain ⟨x, h1x, h2x⟩ := exists_between (a₁:=c) (a₂:= min b (Finset.univ.inf' h3 d))
      (by grind [Finset.lt_inf'_iff])
    have h1d : ∀ i, min b (Finset.univ.inf' h3 d) ≤ d i := by
      intro i
      exact le_trans Std.min_le_right (Finset.inf'_le d (Finset.mem_univ i))
    have : ∀ i, x ∉ Y i := by
      intro i
      exact Set.disjoint_left.mp (hd i).2 ⟨h1x, by grind [Std.min_le_right, Finset.inf'_le]⟩
    have h3x : x ∈ Set.Ioo a b := by grind
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (h1Y h3x)
    exact absurd hxi (this i)


/-- If a finite set $s$ is contained in some interval $(a,b)$ then there is some
$c∈(a,b)$ such that $(a,c)$ and $s$ are disjoint -/
lemma finite_in_interval_gap [DenselyOrdered M] {a b : M} (hab : a < b)
    {s : Set M} (h1s : s.Finite) (h2s : s ⊆ Set.Ioo a b) :
    ∃ c ∈ Set.Ioo a b, Disjoint (Set.Ioo a c) s := by
  by_cases h : s.Nonempty
  · rw [← Set.Finite.toFinset_nonempty h1s] at h
    use h1s.toFinset.min' h
    constructor
    · exact h2s (h1s.mem_toFinset.mp (h1s.toFinset.min'_mem h))
    · rw [Set.disjoint_left]
      intro x h1x h2x
      have := h1s.toFinset.min'_le x (h1s.mem_toFinset.mpr h2x)
      grind
  · push Not at h
    obtain ⟨x, hx⟩ := exists_between hab
    use x
    grind

lemma exists_definableFun_lub [DefinablyComplete L M] {s : M → Set M} (h1s : def_family_univ₁ L s)
    (h2s : ∀ x, (s x).Nonempty) (h3s : ∀ x, BddAbove (s x)) :
    ∃ g : M → M, Set.univ.DefinableFun₁ L g ∧ ∀ x, IsLUB (s x) (g x) := by
  have : ∀ x, ∃ y, IsLUB (s x) y := by
    intro x
    exact DefinablyComplete.lub (s x) (h2s x) (def_family_fiber_univ₁ h1s x) (h3s x)
  choose g hg using this
  use g
  refine ⟨?_, hg⟩
  apply Set.definableFun₁_of_graph
  have : {w : Fin 2 → M | g (w 0) = w 1} = {w : Fin 2 → M | IsLUB (s (w 0)) (w 1)} := by
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hw
      rw [← hw]
      exact hg (w 0)
    · intro hw
      symm
      exact hw.unique (hg (w 0))
  rw [this]
  exact def_family_lub_univ₁ h1s

lemma isBasic_ordConnected {s : Set M} (hb : IsBasic s) : s.OrdConnected := by
  cases hb with
  | _ => simp [Set.ordConnected_singleton, Set.ordConnected_Ioo,
    Set.ordConnected_Ioi, Set.ordConnected_Iio, Set.ordConnected_univ]

variable [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [OMinimal L M]

/- REMOVE SOME OF THE GRINDS -/
/-- Let $I⊆M$ be an open interval. And let $f : I → M$ be definable
and $f(x)>x$ for all $x∈I$. Then there is $d∈I$ such that
the set {x ∈ I : x < d ∧ d < f(x)} contains an open interval. -/
lemma interior_def_fun {a b : M} (hab : a < b) {f : M → M}
    (h1f : Set.univ.DefinableFun₁ L f) (h2f : ∀ x ∈ Set.Ioo a b, x < f x) :
    ∃ d ∈ Set.Ioo a b, ∃ v w, v < w ∧ Set.Ioo v w ⊆ Set.Ioo a b ∧
    ∀ x ∈ Set.Ioo v w, x < d ∧ d < f x := by
  let B := {x | a < x ∧ x < b ∧ ∀ t, a < t → t < x → f t < f x}
  have h1B : IsTame B := OMinimal.is_ominimal (L:=L) (by definability)
  by_cases h2B : B.Finite
  · have : B ⊆ Set.Ioo a b := by grind
    obtain ⟨b', h1b', h2b'⟩ := finite_in_interval_gap hab h2B this
    obtain ⟨t, ht⟩ := exists_between (a₁:=a) (a₂:=b') (by grind)
    let s := {x | a < x ∧ x < t ∧ f t ≤ f x}
    have h1 : ∀ r ∈ Set.Ioo a b', f t ≤ f r → ∃ q ∈ Set.Ioo a r, f t ≤ f q := by
      intro r h1r h2r
      have : r ∉ B := Disjoint.notMem_of_mem_left h2b' h1r
      rw [Set.notMem_ofPred_iff] at this
      simp only [not_and, not_forall, not_lt] at this
      obtain ⟨q, hq⟩ := this (by grind) (by grind)
      exact ⟨q, by grind⟩
    have h2 : s.Nonempty := by
      obtain ⟨y, hy⟩ := h1 t (Set.mem_Ioo.mpr ht) (by trivial)
      exact ⟨y, by grind⟩
    have h3 : ∀ y ∈ s, ∃ z ∈ s, z < y := by
      intro y hy
      obtain ⟨z, h1z, h2z⟩ := h1 y (by grind) (by grind)
      exact ⟨z, by grind⟩
    have h4 : s.Infinite := by
      by_contra! h
      obtain ⟨y, h1y, h2y⟩ := Set.exists_min_image s id h h2
      simp only [id_eq] at h2y
      obtain ⟨z, hz⟩ := h3 y (Set.mem_sep_iff.mpr h1y)
      exact absurd (h2y z hz.1) (not_le.mpr hz.2)
    have h5 : Set.univ.Definable₁ L s := by definability
    obtain ⟨v, w, hvw⟩ := isTame_infinite_has_ioo (OMinimal.is_ominimal h5) h4
    obtain ⟨d, hd⟩ := exists_between (a₁:=t) (a₂:= min b (f t)) (lt_min (by grind) (by grind))
    refine ⟨d, by grind, v, w, by grind, by grind, by grind⟩
  · push Not at h2B
    obtain ⟨c, d, h1cd, h2cd⟩ := isTame_infinite_has_ioo h1B h2B
    have h1 : Set.Ioo c d ⊆ Set.Ioo a b := by grind
    obtain ⟨r, hr⟩ := exists_between h1cd
    have h2r : r ∈ Set.Ioo a b := by exact Set.mem_Ioo.mpr (h1 hr)
    obtain ⟨t, ht⟩ := exists_between (lt_min hr.2 (h2f r h2r))
    exact ⟨t, by grind,r ,t, by grind⟩

end TameGeometry

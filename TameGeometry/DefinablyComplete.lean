import Mathlib.Topology.Order.DenselyOrdered
import TameGeometry.Definability

/-!
# Definable completeness

we define definable completeness and show some basic properties.

-/

namespace TameGeometry

open FirstOrder FirstOrder.Language

/-- A structure is definably complete if
every non-empty bounded definable set has an infimum and supremum in the structure -/
class DefinablyComplete (L : Language) (M : Type*) [L.IsOrdered] [L.Structure M] [M ⊨ L.dlo]
  [LinearOrder M] [L.OrderedStructure M] : Prop where
  glb : ∀ (s : Set M), s.Nonempty → Set.univ.Definable₁ L s → BddBelow s → ∃ a, IsGLB s a
  lub : ∀ (s : Set M), s.Nonempty → Set.univ.Definable₁ L s → BddAbove s → ∃ b, IsLUB s b

variable {M : Type*} {L : Language} [LinearOrder M] [L.IsOrdered]
  [L.Structure M] [M ⊨ L.dlo] [L.OrderedStructure M] [DefinablyComplete L M]

lemma exists_definableFun_lub {s : M → Set M} (h1s : def_family_univ₁ L s)
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

variable [TopologicalSpace M] [OrderTopology M]

lemma isLeast_of_closed {S : Set M} (h1s : Set.univ.Definable₁ L S)
    (h2s : S.Nonempty) (h3s : BddBelow S) (h4s : IsClosed S) :
    ∃ c, IsLeast S c := by
  obtain ⟨c, hc⟩ := DefinablyComplete.glb (L := L) S h2s h1s h3s
  exact ⟨c, hc.mem_of_isClosed h2s h4s, hc.1⟩

lemma isGreatest_of_closed {S : Set M} (h1s : Set.univ.Definable₁ L S)
    (h2s : S.Nonempty) (h3s : BddAbove S) (h4s : IsClosed S) :
    ∃ c, IsGreatest S c := by
  obtain ⟨c, hc⟩ := DefinablyComplete.lub (L := L) S h2s h1s h3s
  exact ⟨c, hc.mem_of_isClosed h2s h4s, hc.1⟩

variable [DenselyOrdered M]

lemma intermediate_value_ioo {a b : M} (hab : a < b)
    {f : M → M} (h1f : Set.univ.DefinableFun₁ L f) (h2f : ContinuousOn f (Set.Icc a b)) :
    ∀ u ∈ Set.Ioo (f a) (f b), ∃ c ∈ Set.Ioo a b, f c = u := by
  intro u hu
  obtain ⟨c, ⟨⟨h1c, h2c⟩, h3c⟩⟩ := isLeast_of_closed (L:=L) (S := Set.Icc a b ∩ {x | u ≤ f x})
    (by definability) ⟨b, by grind⟩ ⟨a, fun x hx ↦ hx.1.1⟩
    (h2f.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
  have h1 : (nhdsWithin c (Set.Ico a c)).NeBot := right_nhdsWithin_Ico_neBot (by grind)
  have h2 : Filter.Tendsto f (nhdsWithin c (Set.Ico a c)) (nhds (f c)) :=
    (h2f c h1c).mono_left (nhdsWithin_mono c (by grind))
  have h3 : f c ≤ u := le_of_tendsto h2 (Filter.eventually_of_mem self_mem_nhdsWithin
    fun x hx ↦ le_of_not_ge (fun h ↦ (not_le.mpr hx.2) (h3c (by grind))))
  exact ⟨c, ⟨by grind, by grind⟩, le_antisymm h3 h2c⟩

lemma intermediate_value_ioo' {a b : M} (hab : a < b)
    {f : M → M} (h1f : Set.univ.DefinableFun₁ L f) (h2f : ContinuousOn f (Set.Icc a b)) :
    ∀ u ∈ Set.Ioo (f b) (f a), ∃ c ∈ Set.Ioo a b, f c = u := by
  intro u hu
  obtain ⟨c, ⟨⟨h1c, h2c⟩, h3c⟩⟩ := isLeast_of_closed (L:=L) (S := Set.Icc a b ∩ {x | f x ≤ u})
    (by definability) ⟨b, by grind⟩ ⟨a, fun x hx ↦ hx.1.1⟩
    (h2f.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
  have h1 : (nhdsWithin c (Set.Ico a c)).NeBot := right_nhdsWithin_Ico_neBot (by grind)
  have h2 : Filter.Tendsto f (nhdsWithin c (Set.Ico a c)) (nhds (f c)) :=
    (h2f c h1c).mono_left (nhdsWithin_mono c (by grind))
  have h3 : u ≤ f c := ge_of_tendsto h2 (Filter.eventually_of_mem self_mem_nhdsWithin
    fun x hx ↦ le_of_not_ge (fun h ↦ hx.2.not_ge (h3c (by grind))))
  exact ⟨c, ⟨by grind, by grind⟩, le_antisymm h2c h3⟩

theorem intermediate_value_uIoo {a b : M} (hab : a < b)
    {f : M → M} (h1f : Set.univ.DefinableFun₁ L f) (h2f : ContinuousOn f (Set.Icc a b)) :
    ∀ u ∈ Set.uIoo (f a) (f b), ∃ c ∈ Set.Ioo a b, f c = u := by
  intro u hu
  obtain h | h := le_total (f a) (f b)
  · rw [Set.uIoo_of_le h] at hu
    exact intermediate_value_ioo hab h1f h2f u hu
  · rw [Set.uIoo_of_ge h] at hu
    exact intermediate_value_ioo' hab h1f h2f u hu

end TameGeometry

import TameGeometry.Basic

open FirstOrder FirstOrder.Language

namespace TameGeometry

variable {M : Type*} (L : Language) [L.IsOrdered] [L.Structure M]
         [M ⊨ L.dlo] [LinearOrder M] [L.OrderedStructure M]
         [TopologicalSpace M] [OrderTopology M] [DefinablyComplete L M]

/--
Let $a, b ∈ M$ with $a < b$ and
let $S$ be some definable subset of $M$ and
such that $[a, b] ∩ S$ is a non-empty closed subset
of the subspace $[a, b] ⊆ M$. Then the set
$[a, b] ∩ S$ has a minimum.
-/
lemma min_icc_closed_subset {a b : M} {S : Set M} (h1s : Set.univ.Definable₁ L S)
    (h2s : ((Set.Icc a b) ∩ S).Nonempty) (h3s : IsClosed {x : ↥(Set.Icc a b) | ↑x ∈ S}) :
    ∃ c ∈ Set.Icc a b, c ∈ S ∧ ∀ x ∈ Set.Ico a c, x ∉ S := by
  let X := ((Set.Icc a b) ∩ S)
  have h1X : BddBelow X := ⟨a, fun x hx ↦ hx.1.1⟩
  obtain ⟨c, h1c⟩ := DefinablyComplete.glb (L:=L) X h2s (by definability) h1X
  obtain ⟨w, hw⟩ := id h2s
  have h2c : c ∈ Set.Icc a b := ⟨h1c.2 fun y hy ↦ hy.1.1, le_trans (h1c.1 hw) (hw.1.2)⟩
  refine ⟨c, h2c, ?_⟩
  have : IsGLB {x : ↥(Set.Icc a b) | ↑x ∈ S} ⟨c, h2c⟩ :=
    ⟨fun x hx ↦ h1c.1 ⟨Subtype.coe_prop x, hx⟩,
    fun x hx ↦ h1c.2 (fun y hy ↦ hx (a:= ⟨y,hy.1⟩) hy.2)⟩
  have := IsGLB.mem_of_isClosed this (by use ⟨w,hw.1⟩; exact hw.2) h3s
  simp only [Set.mem_ofPred_eq] at this
  refine ⟨this, ?_⟩
  intro x hx
  by_contra! h
  have : c ≤ x := by
    apply h1c.1
    exact ⟨⟨hx.1, le_trans hx.2.le h2c.2⟩, h⟩
  exact (not_lt.mpr this) hx.2

variable [DenselyOrdered M]

lemma intermediate_value_ioo {a b : M} (hab : a < b)
    {f : M → M} (h1f : Set.univ.DefinableFun₁ L f) (h2f : ContinuousOn f (Set.Icc a b)) :
    ∀ u ∈ Set.Ioo (f a) (f b), ∃ c ∈ Set.Ioo a b, f c = u := by
  intro u hu
  obtain ⟨c, h1c, h2c, h3c⟩ := min_icc_closed_subset (S:={x | u ≤ f x}) L (by definability)
    ⟨b, ⟨⟨hab.le, le_rfl⟩, hu.2.le⟩⟩ (isClosed_le continuous_const (ContinuousOn.domRestrict h2f))
  have h1 : (nhdsWithin c (Set.Ico a c)).NeBot := right_nhdsWithin_Ico_neBot (by grind)
  have h2 : Filter.Tendsto f (nhdsWithin c (Set.Ico a c)) (nhds (f c)) :=
    (h2f c h1c).mono_left (nhdsWithin_mono c (by grind))
  have h3 : f c ≤ u := le_of_tendsto h2
    (Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx ↦ le_of_not_ge (h3c x hx)))
  exact ⟨c, ⟨by grind, by grind⟩, le_antisymm h3 h2c⟩

lemma intermediate_value_ioo' {a b : M} (hab : a < b)
    {f : M → M} (h1f : Set.univ.DefinableFun₁ L f) (h2f : ContinuousOn f (Set.Icc a b)) :
    ∀ u ∈ Set.Ioo (f b) (f a), ∃ c ∈ Set.Ioo a b, f c = u := by
  intro u hu
  obtain ⟨c, h1c, h2c, h3c⟩ := min_icc_closed_subset (S:={x | f x ≤ u}) L (by definability)
    ⟨b, ⟨⟨hab.le, le_rfl⟩, hu.1.le⟩⟩ (isClosed_le (ContinuousOn.domRestrict h2f) continuous_const)
  have h1 : (nhdsWithin c (Set.Ico a c)).NeBot := right_nhdsWithin_Ico_neBot (by grind)
  have h2 : Filter.Tendsto f (nhdsWithin c (Set.Ico a c)) (nhds (f c)) :=
    (h2f c h1c).mono_left (nhdsWithin_mono c (by grind))
  have h3 : u ≤ f c := ge_of_tendsto h2
    (Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx ↦ le_of_not_ge (h3c x hx)))
  exact ⟨c, ⟨by grind, by grind⟩, le_antisymm h2c h3⟩

theorem intermediate_value_uIoo {a b : M} (hab : a < b)
    {f : M → M} (h1f : Set.univ.DefinableFun₁ L f) (h2f : ContinuousOn f (Set.Icc a b)) :
    ∀ u ∈ Set.uIoo (f a) (f b), ∃ c ∈ Set.Ioo a b, f c = u := by
  intro u hu
  obtain h | h := le_total (f a) (f b)
  · rw [Set.uIoo_of_le h] at hu
    exact intermediate_value_ioo L hab h1f h2f u hu
  · rw [Set.uIoo_of_ge h] at hu
    exact intermediate_value_ioo' L hab h1f h2f u hu

end TameGeometry

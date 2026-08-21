import TameGeometry.Basic

open FirstOrder FirstOrder.Language

namespace TameGeometry

variable {M : Type*} (L : Language) [L.IsOrdered] [L.Structure M]
         [M ⊨ L.dlo] [LinearOrder M] [L.OrderedStructure M]
         [TopologicalSpace M] [OrderTopology M] [DefinablyComplete L M]

/--
Let $S$ be a non-empty, bounded below, closed and definable subset of $M$.
Then $S$ has a least element.
-/
lemma isLeast_of_closed {S : Set M} (h1s : Set.univ.Definable₁ L S)
    (h2s : S.Nonempty) (h3s : BddBelow S) (h4s : IsClosed S) :
    ∃ c, IsLeast S c := by
  obtain ⟨c, hc⟩ := DefinablyComplete.glb (L := L) S h2s h1s h3s
  exact ⟨c, hc.mem_of_isClosed h2s h4s, hc.1⟩

variable [DenselyOrdered M]

lemma intermediate_value_ioo {a b : M} (hab : a < b)
    {f : M → M} (h1f : Set.univ.DefinableFun₁ L f) (h2f : ContinuousOn f (Set.Icc a b)) :
    ∀ u ∈ Set.Ioo (f a) (f b), ∃ c ∈ Set.Ioo a b, f c = u := by
  intro u hu
  obtain ⟨c, ⟨⟨h1c, h2c⟩, h3c⟩⟩ := isLeast_of_closed (S := Set.Icc a b ∩ {x | u ≤ f x}) L
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
  obtain ⟨c, ⟨⟨h1c, h2c⟩, h3c⟩⟩ := isLeast_of_closed (S := Set.Icc a b ∩ {x | f x ≤ u}) L
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
    exact intermediate_value_ioo L hab h1f h2f u hu
  · rw [Set.uIoo_of_ge h] at hu
    exact intermediate_value_ioo' L hab h1f h2f u hu

end TameGeometry

import Mathlib.Topology.Order.MonotoneContinuity

namespace TameGeometry

variable {α : Type*} [TopologicalSpace α]

lemma frontier_union (A : Finset (Set α)) :
    frontier (⋃ a ∈ A, a) ⊆ (⋃ a ∈ A, frontier a) := by
  intro x ⟨h1,h2⟩
  rw [A.closure_biUnion] at h1
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp h1
  apply Set.mem_biUnion ha
  exact ⟨hxa, fun h ↦ h2 (interior_mono (Set.subset_biUnion_of_mem ha) h) ⟩

variable [LinearOrder α] [OrderTopology α] [NoMinOrder α] [NoMaxOrder α]

lemma closure_order (n : ℕ) :
    ∀ (X : Set (Fin n → α)),
    closure X = {y | ∀ (a b : (Fin n → α)), (∀ (i : Fin n), (a i < y i) ∧ (y i < b i))
    → ∃ x ∈ X, ∀ (i : Fin n), (a i < x i) ∧ (x i < b i)} := by
  intro X
  ext z
  rw [mem_closure_iff_nhds]
  constructor
  · intro h
    rw [Set.mem_ofPred_eq]
    intro a b hz
    specialize h (Set.univ.pi (fun (i : Fin n) ↦ Set.Ioo (a i) (b i)))
    have h1 : ((Set.univ.pi fun i ↦ Set.Ioo (a i) (b i)) ∩ X).Nonempty := by
      apply h
      rw [set_pi_mem_nhds_iff]
      · intro i hi
        specialize hz i
        exact Ioo_mem_nhds hz.left hz.right
      · exact Set.finite_univ
    obtain ⟨x, hx⟩ := h1
    grind
  · intro h t ht
    rw [Set.mem_ofPred_eq] at h
    rw [nhds_pi, Filter.mem_pi] at ht
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := ht
    simp only [mem_nhds_iff_exists_Ioo_subset] at hi3
    choose a b hab1 hab2 using hi3
    specialize h a b
    simp only [Set.mem_Ioo] at hab1
    specialize h (by intro i; exact (hab1 i))
    suffices ∃ x∈X, x∈t by rw [Set.inter_nonempty_iff_exists_right]; exact this
    obtain ⟨x, hx1, hx2⟩ := h
    use x
    refine ⟨hx1, ?_⟩
    simp_rw [← Set.mem_Ioo] at hx2
    have hx3 : ∀ (i : Fin n), x i ∈ hi2 i := by grind only [Set.subset_def]
    grind only [Set.subset_def, Set.mem_pi]

variable {β : Type*} [TopologicalSpace β] [LinearOrder β] [OrderTopology β]
  [DenselyOrdered β]

theorem strictMono_ioo_continuousOn {f : α → β} {a b : α}
    (h1 : StrictMonoOn f (Set.Ioo a b))
    (h2 : ∃ c d, c < d ∧ Set.Ioo c d ⊆ f '' Set.Ioo a b) :
    ∃ v w, v < w ∧ Set.Ioo v w ⊆ Set.Ioo a b ∧ ContinuousOn f (Set.Ioo v w) := by
  obtain ⟨c, d, hcd⟩ := h2
  obtain ⟨c', hc'⟩ := exists_between hcd.1
  obtain ⟨d', hd'⟩ := exists_between hc'.2
  have h1c' : c' ∈ Set.Ioo c d := by grind
  have h1d' : d' ∈ Set.Ioo c d := by grind
  obtain ⟨r, hr⟩ := hcd.2 h1c'
  obtain ⟨s, hs⟩ := hcd.2 h1d'
  refine ⟨r, s, by grind [h1.lt_iff_lt], by grind, ?_⟩
  have h3 : Set.Ioo c' d' ⊆ f '' Set.Ioo r s := by
    intro y hy
    obtain ⟨x, hxab, hfxy⟩ := hcd.2 ⟨hc'.1.trans hy.1, hy.2.trans hd'.2⟩
    grind [h1.lt_iff_lt]
  intro x hx
  have h4 : c' < f x := by rw [← hr.2]; exact h1 hr.1 (by grind) hx.1
  have h5 : f x < d' := by rw [← hs.2]; exact h1 (by grind) hs.1 hx.2
  exact (StrictMonoOn.continuousAt_of_image_mem_nhds (h1.mono (by grind)) (Ioo_mem_nhds hx.1 hx.2)
    (Filter.mem_of_superset (Ioo_mem_nhds h4 h5) h3)).continuousWithinAt

theorem strictAnti_ioo_continuousOn {f : α → β} {a b : α}
    (hf : StrictAntiOn f (Set.Ioo a b))
    (hcd : ∃ c d, c < d ∧ Set.Ioo c d ⊆ f '' Set.Ioo a b) :
    ∃ v w, v < w ∧ Set.Ioo v w ⊆ Set.Ioo a b ∧ ContinuousOn f (Set.Ioo v w) := by
  obtain ⟨c, d, h1, h2⟩ := hcd
  obtain ⟨v, w, h3, h4, h5⟩ :=
    strictMono_ioo_continuousOn (f := OrderDual.toDual ∘ f) hf.dual_right
      ⟨OrderDual.toDual d, OrderDual.toDual c, h1, fun x hx ↦ h2 ⟨hx.2, hx.1⟩⟩
  exact ⟨v, w, h3, h4, continuous_ofDual.comp_continuousOn h5⟩

lemma continuousAt_iff {f : α → α} {x : α} :
    ContinuousAt f x ↔ ∀ p q, p < f x → f x < q →
    ∃ c d, c < x ∧ x < d ∧ ∀ z, c < z → z < d → p < f z ∧ f z < q := by
  rw [ContinuousAt, (nhds_basis_Ioo x).tendsto_iff (nhds_basis_Ioo (f x))]
  simp only [Prod.forall, Prod.exists, Set.mem_Ioo, and_imp]
  grind

end TameGeometry

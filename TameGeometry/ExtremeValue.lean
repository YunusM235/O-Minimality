import TameGeometry.Basic
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Topology.Homeomorph.Lemmas

open FirstOrder FirstOrder.Language

namespace TameGeometry

variable {M : Type*} {L : Language} [L.IsOrdered] [L.Structure M]
  [M ⊨ L.dlo] [LinearOrder M] [L.OrderedStructure M]
  [TopologicalSpace M] [OrderTopology M] [Nonempty M]
  [NoMinOrder M] [NoMaxOrder M] [DefinablyComplete L M]

private def memBox {n : ℕ} (p : Fin n ⊕ Fin n → M) (x : Fin n → M) : Prop :=
  ∀ i, p (Sum.inl i) < x i ∧ x i < p (Sum.inr i)

private def lastFromBox {n : ℕ} (s : Set (Fin (n + 1) → M)) (p : Fin n ⊕ Fin n → M) : Set M :=
  {m | ∃ y : Fin n → M, memBox p y ∧ Fin.snoc y m ∈ s}

private def boxLUB {n : ℕ} (s : Set (Fin (n + 1) → M)) (x : Fin n → M) : Set M :=
  {m | ∃ y : Fin n ⊕ Fin n → M, memBox y x ∧ IsLUB (lastFromBox s y) m}

private lemma snoc_glb_mem {n : ℕ} {s : Set (Fin (n + 1) → M)} (h1 : IsClosed s)
    {x : Fin n → M} {c : M}
    (h2 : ∀ y : Fin n ⊕ Fin n → M, memBox y x → ∃ u, IsLUB (lastFromBox s y) u)
    (h3 : IsGLB (boxLUB s x) c) : Fin.snoc x c ∈ s := by
  rw [← h1.closure_eq, closure_order (n + 1)]
  intro a b hab
  simp only [Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last] at hab
  obtain ⟨h1ab, h2ab⟩ := hab
  obtain ⟨d, hd⟩ := (isGLB_lt_iff h3).mp h2ab.2
  obtain ⟨e, he⟩ := hd.1
  let p : Fin n ⊕ Fin n → M :=
    Sum.elim (fun i ↦ max (a i.castSucc) (e (Sum.inl i)))
      (fun i ↦ min (b i.castSucc) (e (Sum.inr i)))
  have h1p : memBox p x :=
    fun i ↦ ⟨max_lt (h1ab i).1 (he.1 i).1, lt_min (h1ab i).2 (he.1 i).2⟩
  obtain ⟨u, hu⟩ := h2 p h1p
  have h2p : lastFromBox s p ⊆ lastFromBox s e := by
    intro t ⟨z, hz, hzs⟩
    exact ⟨z, fun i ↦ ⟨(le_max_right _ _).trans_lt (hz i).1,
      (hz i).2.trans_le (min_le_right _ _)⟩, hzs⟩
  have h2u: u < b (Fin.last n) := (hu.2 (upperBounds_mono_set h2p he.2.1)).trans_lt hd.2
  obtain ⟨t, h1t, h2t⟩ :=
    (lt_isLUB_iff hu).mp (h2ab.1.trans_le (h3.1 ⟨p, h1p, hu⟩))
  obtain ⟨y, hy⟩ := id h1t
  refine ⟨Fin.snoc y t, hy.2, Fin.forall_fin_succ'.mpr ⟨?_, ?_⟩⟩
  · intro i
    rw [Fin.snoc_castSucc]
    exact ⟨(le_max_left _ _).trans_lt (hy.1 i).1, (hy.1 i).2.trans_le (min_le_left _ _)⟩
  · rw [Fin.snoc_last]
    exact ⟨h2t, (hu.1 ⟨y, hy.1, hy.2⟩).trans_lt h2u⟩

lemma cbd_init_closed {n : ℕ} {s : Set (Fin (n + 1) → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s)
    (h4 : Set.univ.Definable L s) : IsClosed (Fin.init '' s) := by
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := h3
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [closure_order n] at hx
  have h4 : ∀ y : Fin n ⊕ Fin n → M, memBox y x → (lastFromBox s y).Nonempty := by
    intro y hy
    obtain ⟨w, ⟨x, h1x, h2x⟩, hw⟩ :=
      hx (fun i ↦ y (Sum.inl i)) (fun i ↦ y (Sum.inr i)) hy
    exact ⟨x (Fin.last n), w, hw, by grind [Fin.snoc_init_self]⟩
  have h5 : ∀ (y : Fin n ⊕ Fin n → M) {t}, t ∈ lastFromBox s y →
    a (Fin.last n) ≤ t ∧ t ≤ b (Fin.last n) := by
    intro y h1y ⟨h2y, h3y⟩
    exact ⟨by grind [Fin.snoc_last, ha h3y.2 (Fin.last n)],
      by grind [Fin.snoc_last, hb h3y.2 (Fin.last n)]⟩
  have h6 : ∀ y : Fin n ⊕ Fin n → M, memBox y x → ∃ u, IsLUB (lastFromBox s y) u :=
    fun p hp ↦ DefinablyComplete.lub (L := L) (lastFromBox s p) (h4 p hp)
      (def_family_fiber' (by definability) p)
      ⟨b (Fin.last n), fun t ht ↦ (h5 p ht).2⟩
  have h7 : (boxLUB s x).Nonempty := by
    choose a ha using fun i ↦ exists_lt (x i)
    choose b hb using fun i ↦ exists_gt (x i)
    obtain ⟨u, hu⟩ := h6 (Sum.elim a b) fun i ↦ ⟨ha i, hb i⟩
    exact ⟨u, _, fun i ↦ ⟨ha i, hb i⟩, hu⟩
  have h8 : BddBelow (boxLUB s x) := ⟨a (Fin.last n), by
    intro u ⟨p, hp, hup⟩
    obtain ⟨t, ht⟩ := h4 p hp
    exact (h5 p ht).1.trans (hup.1 ht)⟩
  obtain ⟨c, hc⟩ := DefinablyComplete.glb (L := L) (boxLUB s x) h7 (by definability) h8
  refine ⟨Fin.snoc x c, snoc_glb_mem h1 h6 hc, Fin.init_snoc _ _⟩

lemma cbd_projection_closed (n : ℕ) {m : ℕ} (hn : n ≤ m)
    {s : Set (Fin m → M)} (h1 : IsClosed s) (h2 : BddBelow s)
    (h3 : BddAbove s) (h4 : Set.univ.Definable L s) :
    IsClosed (Fin.take n hn '' s) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
    simp only [Nat.add_zero, Fin.take_eq_self, Set.image_id']
    exact h1
  | succ k ih =>
    have : (Fin.take n hn : (Fin (n + (k + 1)) → M) → _)
      = Fin.take n (Nat.le_add_right n k) ∘ Fin.init := by rfl
    rw [this, Set.image_comp]
    exact ih (Nat.le_add_right n k) (cbd_init_closed h1 h2 h3 h4)
      (by
        obtain ⟨x, hx⟩ := h2
        use Fin.init x
        intro y hy i
        simp only [Set.mem_image] at hy
        obtain ⟨y', hy'⟩ := hy
        rw [← hy'.2]
        exact hx hy'.1 i.castSucc
        )
      (by
        obtain ⟨x, hx⟩ := h3
        use Fin.init x
        intro y hy i
        simp only [Set.mem_image] at hy
        obtain ⟨y', hy'⟩ := hy
        rw [← hy'.2]
        exact hx hy'.1 i.castSucc)
      (by definability)

/-- Projection to first coordinates of cbd subset is closed -/
lemma cbd_first_closed {n : ℕ} {s : Set (Fin (n + 1) → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s) (h4 : Set.univ.Definable L s) :
    IsClosed ((· 0) '' s) := by
  have := (Homeomorph.funUnique (Fin 1) M).isClosed_image.mpr
    (cbd_projection_closed (m:=n+1) 1 (Nat.le_add_left 1 n) h1 h2 h3 h4)
  rw [← Set.image_comp] at this
  exact this

private theorem monotone_inter₁_rel {R : M → M → Prop}
    (h1r : ∀ x, ¬ R x x) (h2r : ∀ {x y}, x ≠ y → R x y ∨ R y x)
    {f : M → Set M} (h1 : def_family_univ₁ L f)
    (h2 : ∀ {x y}, R x y → f x ⊆ f y) (h3 : ∀ x, (f x).Nonempty) (h4 : ∀ x, IsClosed (f x))
    (h5 : ∀ x, BddBelow (f x)) (h6 : ∀ x, BddAbove (f x)) :
    (⋂ x, f x).Nonempty := by
  choose g hg using fun i ↦ DefinablyComplete.glb (f i) (h3 i) (def_family_fiber_univ₁ h1 i) (h5 i)
  have h1g : ∀ x, g x ∈ f x := fun x ↦ IsClosed.isGLB_mem (hg x) (h3 x) (h4 x)
  have h2g : ∀ x y, R x y → g y ≤ g x := fun x y hxy ↦ (hg y).1 ((h2 hxy) (h1g x))
  have h3g : BddAbove (Set.range g) := by
    let x := Classical.arbitrary M
    obtain ⟨p, hp⟩ := h6 x
    use p
    intro q hq
    obtain ⟨y, hy⟩ := hq
    rw [← hy]
    by_cases! h : y = x
    · rw [h]
      exact hp (h1g x)
    · obtain h' | h' := h2r h
      · exact hp ((h2 h') (h1g y))
      · exact (h2g x y h').trans (hp (h1g x))
  obtain ⟨c, hc⟩ := DefinablyComplete.lub (Set.range g) (Set.range_nonempty g)
    (def_family_least_range h1 (fun x ↦ ⟨h1g x, (hg x).1⟩)) h3g
  simp only [Set.nonempty_iInter]
  use c; intro i
  let X := {x | ¬ R i x }
  have h1X : X.Nonempty := ⟨i, h1r i⟩
  have h2X : g '' X ⊆ f i := by
    intro y hy
    obtain ⟨x, hx⟩ := hy
    rw [← hx.2]
    by_cases! h : x = i
    · rw [h]
      exact h1g i
    · exact h2 ((h2r h).resolve_right hx.1) (h1g x)
  have h3X : IsLUB (g '' X) c := by
    refine ⟨upperBounds_mono_set (Set.image_subset_range g X) hc.1, ?_⟩
    intro d hd
    apply hc.2
    intro e he
    obtain ⟨e', he'⟩ := he
    rw [← he']
    by_cases! h : ¬ R i e'
    · exact hd ⟨e', ⟨h, rfl⟩⟩
    · exact (h2g i e' h).trans (hd ⟨i, ⟨h1r i, rfl⟩⟩)
  rw [← (h4 i).closure_eq]
  exact closure_mono h2X (h3X.mem_closure (h1X.image g))

theorem monotone_inter₁ {f : M → Set M} (h1 : def_family_univ₁ L f)
    (h2 : ∀ {x y}, x < y → f y ⊆ f x) (h3 : ∀ x, (f x).Nonempty) (h4 : ∀ x, IsClosed (f x))
    (h5 : ∀ x, BddBelow (f x)) (h6 : ∀ x, BddAbove (f x)) :
    (⋂ x, f x).Nonempty := by
  exact monotone_inter₁_rel
    (R:=(·>·)) (fun x ↦ lt_irrefl x) (fun h ↦ h.lt_or_gt.symm) h1 h2 h3 h4 h5 h6

/--
Same as monotone_inter₁ but for a increasing family instead of decreasing.
-/
theorem monotone_inter'₁ {f : M → Set M} (h1 : def_family_univ₁ L f)
    (h2 : ∀ {x y}, x < y → f x ⊆ f y) (h3 : ∀ x, (f x).Nonempty) (h4 : ∀ x, IsClosed (f x))
    (h5 : ∀ x, BddBelow (f x)) (h6 : ∀ x, BddAbove (f x)) :
    (⋂ x, f x).Nonempty := by
  exact monotone_inter₁_rel
    (R:=(·<·)) (fun x ↦ lt_irrefl x) (fun h ↦ h.lt_or_gt) h1 h2 h3 h4 h5 h6

private theorem monotone_inter_rel {n : ℕ} {R : M → M → Prop}
    (h1r : ∀ x, ¬ R x x) (h2r : ∀ {x y}, x ≠ y → R x y ∨ R y x)
    {f : M → Set (Fin n → M)} (h1 : def_family_univ L f)
    (h2 : ∀ {x y}, R x y → f x ⊆ f y) (h3 : ∀ x, (f x).Nonempty) (h4 : ∀ x, IsClosed (f x))
    (h5 : ∀ x, BddBelow (f x)) (h6 : ∀ x, BddAbove (f x)) :
    (⋂ x, f x).Nonempty := by
  induction n with
  | zero =>
    rw [Set.nonempty_iInter, Fin.exists_fin_zero_pi]
    exact fun i ↦ Subsingleton.mem_iff_nonempty.mpr (h3 i)
  | succ n ih =>
    obtain ⟨a, ha⟩ := monotone_inter₁_rel h1r h2r (def_family_proj₀ h1)
      (fun hxy ↦ Set.image_mono (h2 hxy))
      (fun x ↦ (h3 x).image _)
      (fun x ↦ cbd_first_closed (h4 x) (h5 x) (h6 x) (def_family_fiber h1 x))
      (fun x : M ↦ Monotone.map_bddBelow (Function.monotone_eval 0) (h5 x))
      (fun x : M ↦ Monotone.map_bddAbove (Function.monotone_eval 0) (h6 x))
    rw [Set.mem_iInter] at ha
    obtain ⟨b, hb⟩ := ih
      (def_family_preimage_cons h1 a)
      (fun hab ↦ Set.preimage_mono (h2 hab))
      (by
        intro x
        obtain ⟨v, hv⟩ := ha x
        rw [← hv.2]
        use Fin.tail v
        apply Set.mem_preimage.mpr
        simp only [Fin.cons_self_tail]
        exact hv.1)
      (fun x ↦ (h4 x).preimage (continuous_const.finCons continuous_id))
      (by
        intro x
        obtain ⟨r, hr⟩ := h5 x
        use Fin.tail r
        intro y hy i
        exact hr hy i.succ)
      (by
        intro x
        obtain ⟨r, hr⟩ := h6 x
        use Fin.tail r
        intro y hy i
        exact hr hy i.succ)
    rw [Set.mem_iInter] at hb
    exact ⟨Fin.cons a b, Set.mem_iInter.mpr hb⟩

theorem monotone_inter {n : ℕ} {f : M → Set (Fin n → M)} (h1 : def_family_univ L f)
    (h2 : ∀ {x y}, x < y → f y ⊆ f x) (h3 : ∀ x, (f x).Nonempty) (h4 : ∀ x, IsClosed (f x))
    (h5 : ∀ x, BddBelow (f x)) (h6 : ∀ x, BddAbove (f x)) :
    (⋂ x, f x).Nonempty := by
  exact monotone_inter_rel
    (R:=(·>·)) (fun x ↦ lt_irrefl x) (fun h ↦ h.lt_or_gt.symm) h1 h2 h3 h4 h5 h6

/--
Same as monotone_inter but for a increasing family instead of decreasing.
-/
theorem monotone_inter' {n : ℕ} {f : M → Set (Fin n → M)} (h1 : def_family_univ L f)
    (h2 : ∀ {x y}, x < y → f x ⊆ f y) (h3 : ∀ x, (f x).Nonempty) (h4 : ∀ x, IsClosed (f x))
    (h5 : ∀ x, BddBelow (f x)) (h6 : ∀ x, BddAbove (f x)) :
    (⋂ x, f x).Nonempty := by
  exact monotone_inter_rel
    (R:=(·<·)) (fun x ↦ lt_irrefl x) (fun h ↦ h.lt_or_gt) h1 h2 h3 h4 h5 h6

lemma cbd_image_bdd_below₁ {n : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s) (h4 : Set.univ.Definable L s)
    {f : (Fin n → M) → M} (h1f : Set.univ.DefinableFun L f) (h2f : ContinuousOn f s) :
    BddBelow (f '' s) := by
  let g : M → Set (Fin n → M) := fun r ↦ {x ∈ s | r ≥ f x}
  by_contra h
  have h1g : ∀ r, (g r).Nonempty := by
    intro r
    obtain ⟨x, hx⟩ := not_bddBelow_iff.mp h r
    obtain ⟨x', hx'⟩ := hx.1
    use x'
    rw [← hx'.2] at hx
    exact ⟨hx'.1, hx.2.le⟩
  have h2g : ∀ r, IsClosed (g r) :=
    fun r ↦ h2f.preimage_isClosed_of_isClosed h1 isClosed_Iic
  have h3g : ∀ r, BddBelow (g r) := fun r ↦ BddBelow.mono (Set.sep_subset s _) h2
  have h4g : ∀ r, BddAbove (g r) := fun r ↦ BddAbove.mono (Set.sep_subset s _) h3
  obtain ⟨r, hr⟩ := monotone_inter' (L:=L) (by definability) (by grind) h1g h2g h3g h4g
  simp only [g, Set.mem_iInter] at hr
  obtain ⟨a, ha⟩ := exists_lt (f r)
  exact (Std.not_le.mpr ha) (hr a).2

lemma cbd_image_bdd_above₁ {n : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s) (h4 : Set.univ.Definable L s)
    {f : (Fin n → M) → M} (h1f : Set.univ.DefinableFun L f) (h2f : ContinuousOn f s) :
    BddAbove (f '' s) := by
  let g : M → Set (Fin n → M) := fun r ↦ {x ∈ s | r ≤ f x}
  by_contra h
  have h1g : ∀ r, (g r).Nonempty := by
    intro r
    obtain ⟨x, hx⟩ := not_bddAbove_iff.mp h r
    obtain ⟨x', hx'⟩ := hx.1
    use x'
    rw [← hx'.2] at hx
    exact ⟨hx'.1, hx.2.le⟩
  have h2g : ∀ r, IsClosed (g r) :=
    fun r ↦ h2f.preimage_isClosed_of_isClosed h1 isClosed_Ici
  have h3g : ∀ r, BddBelow (g r) := fun r ↦ BddBelow.mono (Set.sep_subset s _) h2
  have h4g : ∀ r, BddAbove (g r) := fun r ↦ BddAbove.mono (Set.sep_subset s _) h3
  obtain ⟨r, hr⟩ := monotone_inter (L:=L) (by definability) (by grind) h1g h2g h3g h4g
  simp only [g, Set.mem_iInter] at hr
  obtain ⟨a, ha⟩ := exists_gt (f r)
  exact (Std.not_le.mpr ha) (hr a).2

lemma cbd_image_bdd_below {n : ℕ} {m : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s) (h4 : Set.univ.Definable L s)
    {f : (Fin n → M) → (Fin m → M)} (h1f : Set.univ.DefinableMap L f) (h2f : ContinuousOn f s) :
    BddBelow (f '' s) := by
  apply bddBelow_pi.mpr
  intro i
  rw [Set.image_image]
  exact cbd_image_bdd_below₁ h1 h2 h3 h4 (h1f i) ((continuous_apply i).comp_continuousOn h2f)

lemma cbd_image_bdd_above {n : ℕ} {m : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s) (h4 : Set.univ.Definable L s)
    {f : (Fin n → M) → (Fin m → M)} (h1f : Set.univ.DefinableMap L f) (h2f : ContinuousOn f s) :
    BddAbove (f '' s) := by
  apply bddAbove_pi.mpr
  intro i
  rw [Set.image_image]
  exact cbd_image_bdd_above₁ h1 h2 h3 h4 (h1f i) ((continuous_apply i).comp_continuousOn h2f)

lemma cbd_image_closed {n : ℕ} {m : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s) (h4 : Set.univ.Definable L s)
    {f : (Fin n → M) → (Fin m → M)} (h1f : Set.univ.DefinableMap L f) (h2f : ContinuousOn f s) :
    IsClosed (f '' s) := by
  let g1 : (Fin n → M) → (Fin (m+n) → M) := fun x ↦ Fin.append (f x) x
  let g2 : (Fin (m+n) → M) → (Fin n → M) := fun x ↦ x ∘ Fin.natAdd m
  have hg : ∀ x, g2 (g1 x) = x := fun x ↦ by ext i; simp [g1, g2]
  have h1g1 : Set.univ.DefinableMap L g1 := by
    simp only [g1]
    exact Set.definableMap_append h1f (fun _ ↦ Set.DefinableFun.proj L)
  have h2g1 : ContinuousOn g1 s := by
    simp only [g1]
    exact (Fin.continuous_append m n).comp_continuousOn (h2f.prodMk continuousOn_id)
  have h3g1 : Fin.take m (Nat.le_add_right m n) '' (g1 '' s) = f '' s := by
    rw [← Set.image_comp]
    simp only [Function.comp_apply]
    apply Set.image_congr
    intro a ha
    ext x
    simp only [Fin.take_apply]
    exact Fin.append_left' (f a) a x
  have h4g1 : IsClosed (g1 '' s) := by
    have : g1 '' s = {w | w ∈ g2 ⁻¹' s ∧ g1 (g2 w) = w} := by
      ext x
      exact ⟨fun xh ↦ by obtain ⟨x', hx'⟩ := xh; grind,
        fun xh ↦ by simp only [Set.mem_image]; exact ⟨(g2 x), xh⟩⟩
    rw [this]
    exact (h1.preimage (Pi.continuous_precomp _)).isClosed_eq
      (h2g1.comp (Pi.continuous_precomp _).continuousOn fun x hx ↦ hx) continuousOn_id
  have := cbd_projection_closed m (Nat.le_add_right m n) h4g1
    (cbd_image_bdd_below h1 h2 h3 h4 h1g1 h2g1)
    (cbd_image_bdd_above h1 h2 h3 h4 h1g1 h2g1)
    (Set.univ.def_image h4 h1g1)
  rw [← h3g1]
  exact this

/-- Let f : M^n → M be a definable function. Let
 X be a CBD subset of M^n and let f be continuous on s. Then the image f(X) is also CBD -/
lemma cbd_image_is_cbd₁ {n : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s) (h4 : Set.univ.Definable L s)
    {f : (Fin n → M) → M} (h1f : Set.univ.DefinableFun L f) (h2f : ContinuousOn f s) :
    IsClosed (f '' s) ∧ BddBelow (f '' s) ∧ BddAbove (f '' s) ∧ Set.univ.Definable₁ L (f '' s) := by
  let f' : (Fin n → M) → (Fin 1 → M) := fun v ↦ (fun i ↦ f v)
  have h1f' : Set.univ.DefinableMap L f' := fun i ↦ h1f
  have h2f' : ContinuousOn f' s := continuousOn_pi.mpr (fun i ↦ h2f)
  have h3f' : f' '' s = {v : Fin 1 → M | v 0 ∈ f '' s} := by ext; simp [f', funext_iff]
  refine ⟨?_, ?_, ?_, by definability⟩
  · have := cbd_image_closed h1 h2 h3 h4 h1f' h2f'
    rw [h3f'] at this
    have := this.preimage (continuous_pi fun i ↦ continuous_id)
    simp only [id_eq, Fin.isValue, Set.mem_image, Set.preimage_ofPred_eq] at this
    exact this
  · exact cbd_image_bdd_below₁ h1 h2 h3 h4 h1f h2f
  · exact cbd_image_bdd_above₁ h1 h2 h3 h4 h1f h2f

theorem extreme_value_min {n : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s)
    (h4 : Set.univ.Definable L s) (h5 : s.Nonempty) {f : (Fin n → M) → M}
    (h1f : Set.univ.DefinableFun L f) (h2f : ContinuousOn f s) :
    ∃ a ∈ s, IsLeast (f '' s) (f a) := by
  obtain ⟨hs1, hs2, hs3, hs4⟩ := cbd_image_is_cbd₁ h1 h2 h3 h4 h1f h2f
  obtain ⟨c, hc⟩ := DefinablyComplete.glb (f '' s) (Set.Nonempty.image f h5) hs4 hs2
  obtain ⟨a, ha⟩ := hc.mem_of_isClosed (h5.image f) hs1
  refine ⟨a, ha.1, ?_⟩
  rw [ha.2]
  exact ⟨hc.mem_of_isClosed (h5.image f) hs1, hc.1⟩

theorem extreme_value_max {n : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s)
    (h4 : Set.univ.Definable L s) (h5 : s.Nonempty) {f : (Fin n → M) → M}
    (h1f : Set.univ.DefinableFun L f) (h2f : ContinuousOn f s) :
    ∃ b ∈ s, IsGreatest (f '' s) (f b) := by
  obtain ⟨hs1, hs2, hs3, hs4⟩ := cbd_image_is_cbd₁ h1 h2 h3 h4 h1f h2f
  obtain ⟨c, hc⟩ := DefinablyComplete.lub (f '' s) (h5.image f) hs4 hs3
  obtain ⟨b, hb⟩ := hc.mem_of_isClosed (h5.image f) hs1
  refine ⟨b, hb.1, ?_⟩
  rw [hb.2]
  exact ⟨hc.mem_of_isClosed (h5.image f) hs1, hc.1⟩

/-- Let f : M^n → M be a definable function. Let
  X be a CBD subset of M^n and let f be continuous on X.
  Then the image f(X) has a minimum and maximum -/
theorem extreme_value {n : ℕ} {s : Set (Fin n → M)}
    (h1 : IsClosed s) (h2 : BddBelow s) (h3 : BddAbove s)
    (h4 : Set.univ.Definable L s) (h5 : s.Nonempty) {f : (Fin n → M) → M}
    (h1f : Set.univ.DefinableFun L f) (h2f : ContinuousOn f s) :
    ∃ a ∈ s, ∃ b ∈ s, IsLeast (f '' s) (f a) ∧ IsGreatest (f '' s) (f b)  := by
  obtain ⟨a, ha⟩ := extreme_value_min h1 h2 h3 h4 h5 h1f h2f
  obtain ⟨b, hb⟩ := extreme_value_max h1 h2 h3 h4 h5 h1f h2f
  exact ⟨a, ha.1, b, hb.1, ha.2, hb.2⟩

end TameGeometry

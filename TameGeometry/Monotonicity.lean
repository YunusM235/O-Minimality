import TameGeometry.OMinimal

/-!
# Monotonicity theorem

-/

namespace TameGeometry

open FirstOrder FirstOrder.Language

variable {L : Language} {M : Type*} [L.IsOrdered] [L.Structure M]
  [LinearOrder M] [L.OrderedStructure M] [M ⊨ L.dlo] [DenselyOrdered M]

/-- Let $s$ be some OrdConnected set and $f : M → M$ a definable function.
  Let $r$ be some 2-ary transitive definable relation such that for all $x ∈ s$ there is
  some interval $(a,b)$ around x such that for all $s,t ∈ (a,b)$ with $s<t$ we have $r f(s) f(t).
  Then we also have $r f(x) f(y)$ for all $x,y ∈ s$ with $x<y$ -/
lemma localRel_to_global [DefinablyComplete L M]
    {s : Set M} (hs : s.OrdConnected) {f : M → M}
    (hf : Set.univ.DefinableFun₁ L f) {r : M → M → Prop}
    [IsTrans M r] (h1r : Set.univ.Definable L {v : Fin 2 → M | r (v 0) (v 1)})
    (h2r : ∀ x ∈ s, ∃ a b, x ∈ Set.Ioo a b ∧ ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
      s < t → (r (f s) (f t))) : ∀ x ∈ s, ∀ y ∈ s, x < y → r (f x) (f y) := by
  intro x hx y hy hxy
  by_contra hxy'
  let Z := {z ∈ Set.Icc x y | x < z ∧ ¬(r (f x) (f z))}
  have hy' : y ∈ Z := ⟨by grind, hxy, hxy'⟩
  obtain ⟨a, ha⟩ :=
    DefinablyComplete.glb (L:=L) Z ⟨y, hy'⟩ (by definability) (by use x; intro _ _; grind)
  have hxa : x ≤ a := ha.2 (fun q hq ↦ hq.1.1)
  have hay : a ≤ y := le_trans (ha.1 hy') (hy'.1.2)
  obtain ⟨v, w, h1vw, h2vw⟩ := h2r a (hs.out hx hy ⟨hxa, hay⟩)
  obtain ⟨q, hq⟩ := ha.exists_between h1vw.2
  have hqvw : q ∈ Set.Ioo v w := ⟨lt_of_lt_of_le h1vw.1 hq.2.1, hq.2.2⟩
  apply hq.1.2.2
  obtain rfl | hax := hxa.eq_or_lt
  · exact h2vw x h1vw q hqvw hq.1.2.1
  · obtain ⟨p, hp⟩ := exists_between (max_lt hax h1vw.1)
    have h3 : p < a := hp.2
    have h4 : p ∉ Z := fun h ↦ h3.not_ge (ha.1 h)
    have h5 : r (f x) (f p) := by grind
    exact IsTrans.trans (f x) (f p) (f q) h5 (h2vw p (by grind) q hqvw (lt_of_lt_of_le h3 hq.2.1))

variable [OMinimal L M] [NoMinOrder M] [NoMaxOrder M]

/-- Let $X_1,…,X_n ⊆ M^2$ be a definable covering of $(a,b)^2$ for some $a < b$.
Then there is a nonempty subinterval $(v,w) ⊆ (a,b)$ and $i ∈ {1,…,n}$
such that ${(x,y) ∈ (v,w)^2 : x < y} ⊆ X_i$.
-/
theorem definable_ramsey {n : ℕ} {a b : M} (hab : a < b)
    (X : Fin n → Set (Fin 2 → M)) (h1X : ∀ i, Set.univ.Definable L (X i))
    (h2X : ∀ x y, x ∈ Set.Ioo a b → y ∈ Set.Ioo a b → ∃ i, ![x, y] ∈ X i) :
    ∃ v w, v < w ∧ Set.Ioo v w ⊆ Set.Ioo a b ∧
    ∃ i, ∀ x y, x < y → x ∈ Set.Ioo v w → y ∈ Set.Ioo v w  → ![x, y] ∈ X i := by
  let Z : Fin n → Set M :=
    fun i ↦ {x | x ∈ Set.Ioo a b ∧ ∃ y, y ∈ Set.Ioo x b ∧ ∀ t ∈ Set.Ioo x y, ![x,t] ∈ X i}
  have hZ1 : ∀ i, Set.univ.Definable₁ L (Z i) := fun i ↦ by definability
  have hZ2 : Set.Ioo a b ⊆ ⋃ i, Z i := by
    intro x hx
    obtain ⟨i, d, hd, h1xd, h2xd⟩ :=
      ioo_def_covering (fun i ↦ {y | ![x, y] ∈ X i})
        (fun r hr ↦ Set.mem_iUnion.mpr (h2X x r hx hr))
        (fun i ↦ def_fiber_left (h1X i) x) hx
    exact Set.mem_iUnion.mpr ⟨i, hx, d, by grind, fun t ht ↦ h2xd ht⟩
  obtain ⟨c, hc⟩ := exists_between hab
  obtain ⟨i, d, h1d, h2d, hid⟩ := ioo_def_covering Z hZ2 hZ1 hc
  let S : M → Set M := fun l ↦ {r | l < r ∧ r < b ∧ ∀ t, l < t → t < r → ![l, t] ∈ X i} ∪ {l}
  have h1S : def_family_univ₁ L S := by definability
  have h2S : ∀ x, (S x).Nonempty := by intro x; use x; grind
  have h3S : ∀ x, BddAbove (S x) := fun x ↦ ⟨max x b, fun _ _ ↦ by grind⟩
  obtain ⟨g, h1g, h2g⟩ := exists_definableFun_lub h1S h2S h3S
  have h3g : ∀ x ∈ Set.Ioo c d, x < g x := by
    intro x hx
    obtain ⟨-, y, h1y, h2y⟩ := hid hx
    exact lt_of_lt_of_le h1y.1 ((h2g x).1 (by grind))
  obtain ⟨m, hm, v, w, h1vw, h2vw, h3vw⟩ := interior_def_fun h2d h1g h3g
  obtain ⟨p, hp⟩ := exists_between h1vw
  obtain ⟨q, hq⟩ := exists_between hp.2
  refine ⟨p, q, by grind, ?_, ?_⟩
  · have : Set.Ioo p q ⊆ Set.Ioo v w := by grind
    grind
  · use i
    intro x y hxy hx hy
    obtain ⟨r, h1r, h2r⟩ := (lt_isLUB_iff (h2g x)).mp ((h3vw x (by grind)).2)
    cases h1r <;> grind

private abbrev A_rel (R : M → M → Prop) (f : M → M) : Set M :=
  {x : M | ∃ v w, x ∈ Set.Ioo v w ∧ ∀ a ∈ Set.Ioo v w, ∀ b ∈ Set.Ioo v w, a < b → R (f a) (f b)}

private abbrev A_eq (f : M → M) : Set M := A_rel (·=·) f

private abbrev A_lt (f : M → M) : Set M := A_rel (·<·) f

private abbrev A_gt (f : M → M) : Set M := A_rel (·>·) f

private lemma B_finite {f : M → M} (h : Set.univ.DefinableFun₁ L f) :
    (A_eq f ∪ A_lt f ∪ A_gt f)ᶜ.Finite := by
  by_contra! h
  obtain ⟨a, b, hab⟩ := isTame_infinite_has_ioo (OMinimal.is_ominimal (L:=L) (by definability)) h
  let X :=
    ![{p : Fin 2 → M | f (p 0) = f (p 1)},
    {p : Fin 2 → M | f (p 0) < f (p 1)},
    {p : Fin 2 → M | f (p 1) < f (p 0)}]
  have : ∀ (x y : M), x ∈ Set.Ioo a b → y ∈ Set.Ioo a b → ∃ i, ![x, y] ∈ X i := by
    intro x y hx hy
    obtain h1 | h2 | h3 := lt_trichotomy (f x) (f y)
    exacts [⟨1, h1⟩, ⟨0, h2⟩, ⟨2, h3⟩]
  obtain ⟨v, w, h1vw, h2vw, ⟨i, h3vw⟩⟩ :=
    definable_ramsey (L:=L) hab.1 X (by definability) this
  obtain ⟨x, hx⟩ := exists_between h1vw
  refine hab.2 (h2vw hx) ?_
  fin_cases i
  · exact Or.inl (Or.inl ⟨v, w, hx, fun r hr s hs hrs ↦  h3vw r s hrs hr hs⟩)
  · exact Or.inl (Or.inr ⟨v, w, hx, fun r hr s hs hrs ↦ h3vw r s hrs hr hs⟩)
  · exact Or.inr ⟨v, w, hx, fun r hr s hs hrs ↦ h3vw r s hrs hr hs⟩

variable [TopologicalSpace M] [OrderTopology M]

lemma continuous_of_def_strictMonoOn_or_strictAntiOn {a b : M} (hab : a < b)
    {f : M → M} (h1f : Set.univ.DefinableFun₁ L f)
    (h2f : StrictMonoOn f (Set.Ioo a b) ∨ StrictAntiOn f (Set.Ioo a b)) :
    ∃ v w, v < w ∧ Set.Ioo v w ⊆ Set.Ioo a b ∧ ContinuousOn f (Set.Ioo v w) := by
  have h1 : Set.InjOn f (Set.Ioo a b) := by
    grind [StrictMonoOn.injOn, StrictAntiOn.injOn]
  have h2 : Set.univ.Definable₁ L (f '' Set.Ioo a b) := by definability
  have h3 := isTame_infinite_has_ioo (OMinimal.is_ominimal h2)
    (Set.Infinite.image h1 (Set.Ioo_infinite hab))
  obtain h2f1 | h2f2 := h2f
  · exact strictMono_ioo_continuousOn h2f1 h3
  · exact strictAnti_ioo_continuousOn h2f2 h3

lemma discontinuities_finite {f : M → M} (hf : Set.univ.DefinableFun₁ L f) :
    {x : M | ¬ContinuousAt f x}.Finite := by
  by_contra! h
  let S := {x | ¬ContinuousAt f x}
  have : Set.univ.Definable₁ L S := by unfold S; simp_rw [continuousAt_iff]; definability
  obtain ⟨a, b, hab⟩ := isTame_infinite_has_ioo (OMinimal.is_ominimal this) h
  obtain ⟨x, hx⟩ := (Set.Infinite.sdiff (Set.Ioo_infinite hab.1) (B_finite hf)).nonempty
  rw [Set.sdiff_compl] at hx
  obtain ⟨⟨v, w, h1vw, h2vw⟩ | ⟨v, w, h1vw, h2vw⟩⟩ | ⟨v, w, h1vw, h2vw⟩ := hx.2
  · have h3 : ContinuousOn f (Set.Ioo (max a v) (min b w)) :=
      (continuousOn_const (c:=f x)).congr (fun p hp ↦ by grind)
    exact absurd (h3.continuousAt (Ioo_mem_nhds (by grind) (by grind))) (hab.2 hx.1)
  · have h4 : StrictMonoOn f (Set.Ioo (max a v) (min b w)) :=
      fun s hs t ht hst ↦ h2vw s (by grind) t (by grind) hst
    obtain ⟨v', w', h1', h2', h3'⟩ :=
      continuous_of_def_strictMonoOn_or_strictAntiOn (by grind) hf (Or.inl h4)
    obtain ⟨p, hp⟩ := exists_between h1'
    have : p ∈ S := by grind [h2' hp]
    exact absurd (h3'.continuousAt (Ioo_mem_nhds hp.1 hp.2)) this
  · have h4 : StrictAntiOn f (Set.Ioo (max a v) (min b w)) :=
      fun s hs t ht hst ↦ h2vw s (by grind) t (by grind) hst
    obtain ⟨v', w', h1', h2', h3'⟩ :=
      continuous_of_def_strictMonoOn_or_strictAntiOn (by grind) hf (Or.inr h4)
    obtain ⟨p, hp⟩ := exists_between h1'
    have : p ∈ S := by grind [h2' hp]
    exact absurd (h3'.continuousAt (Ioo_mem_nhds hp.1 hp.2)) this

/--
Let $f : M → M$ be a definable function.
Then $M$ has a finite covering of basic sets
such that for all sets $s$ in this covering
$f$ is continuous on $s$ and constant, strictly increasing or strictly decreasing.
-/
theorem monotonicity_theorem {f : M → M} (hf : Set.univ.DefinableFun₁ L f) :
    ∃ A : Finset (Set M), (⋃ s ∈ A, s = Set.univ) ∧ ∀ s ∈ A, IsBasic s ∧
    ContinuousOn f s ∧ ((f '' s).Subsingleton ∨ StrictMonoOn f s ∨ StrictAntiOn f s) := by
  by_cases! hM : Nonempty M
  case neg => exact ⟨∅, by simp [Set.univ_eq_empty_iff.mpr hM]⟩
  let B := (A_eq f ∪ A_lt f ∪ A_gt f)ᶜ
  let D := {x : M | ¬ContinuousAt f x}
  let X := B ∪ D
  have hX := Set.Finite.union (B_finite hf) (discontinuities_finite hf)
  obtain ⟨I_eq, h1I_eq, h2I_eq⟩ := OMinimal.is_ominimal (L:=L) (s:= A_eq f \ X) (by definability)
  obtain ⟨I_lt, h1I_lt, h2I_lt⟩ := OMinimal.is_ominimal (L:=L) (s:= A_lt f \ X) (by definability)
  obtain ⟨I_gt, h1I_gt, h2I_gt⟩ := OMinimal.is_ominimal (L:=L) (s:= A_gt f \ X) (by definability)
  let X' := hX.toFinset.image (fun p ↦ ({p} : Set M))
  let I := I_eq ∪ I_lt ∪ I_gt ∪ X'
  refine ⟨I, ?_, ?_⟩
  · have hX' : ⋃ s ∈ X', s = X := by
      rw [Finset.set_biUnion_finset_image, ← Finset.set_biUnion_coe,
        Set.biUnion_of_singleton, Set.Finite.coe_toFinset]
    have : ⋃ s ∈ I, s = A_eq f \ X ∪ A_lt f \ X ∪ A_gt f \ X ∪ X := by
      simp_rw [I, Finset.set_biUnion_union, h2I_eq, h2I_lt, h2I_gt, hX']
    rw [this, ← Set.union_sdiff_distrib, ← Set.union_sdiff_distrib, Set.sdiff_union_self]
    grind
  · intro s hs
    simp only [I, Finset.union_assoc, Finset.mem_union] at hs
    have h3 {s S : Set M} : s ⊆ S \ X → ContinuousOn f s :=
      fun h ↦ continuousOn_of_forall_continuousAt (by grind)
    have h4 {A : Set M} {J : Finset (Set M)} {t : Set M} : A \ X = ⋃ a ∈ J, a → t ∈ J → t ⊆ A \ X :=
      fun h1 h2 ↦ by rw [h1]; exact Set.subset_biUnion_of_mem (u := id) h2
    obtain h | h | h | h := hs
    · refine ⟨h1I_eq s h, h3 (h4 h2I_eq h), Or.inl ?_⟩
      have := localRel_to_global (isBasic_ordConnected (h1I_eq s h)) hf (r:=(·=·))
        (by definability) ((h4 h2I_eq h).trans Set.sdiff_subset)
      rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
      obtain hxy | rfl | hxy := lt_trichotomy x' y'
      exacts [this x' hx' y' hy' hxy, rfl, (this y' hy' x' hx' hxy).symm]
    · exact ⟨h1I_lt s h, h3 (h4 h2I_lt h), Or.inr (Or.inl
        (localRel_to_global (isBasic_ordConnected (h1I_lt s h)) hf (r:=(·<·))
        (by definability) ((h4 h2I_lt h).trans Set.sdiff_subset)))⟩
    · exact ⟨h1I_gt s h, h3 (h4 h2I_gt h), Or.inr (Or.inr
        (localRel_to_global (isBasic_ordConnected (h1I_gt s h)) hf (r:=(·>·))
        (by definability) ((h4 h2I_gt h).trans Set.sdiff_subset)))⟩
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨IsBasic.point p, continuousOn_singleton f p,
        Or.inr (Or.inl (Set.strictMonoOn_singleton f))⟩

end TameGeometry

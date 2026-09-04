import Mathlib.ModelTheory.Order
import Mathlib.Tactic.FinCases
import TameGeometry.Tactic

/-!
# Definability

-/


open FirstOrder FirstOrder.Language

variable {L : Language} {M : Type*} [L.Structure M] {n : ℕ} (A : Set M)

namespace Set

attribute [definability]
  Set.DefinableFun.proj
  Set.DefinableFun.ofPred_eq

attribute [aesop unsafe 30% apply (rule_sets := [Definability])]
  Set.DefinableFun.comp

attribute [aesop norm unfold (rule_sets := [Definability])]
  Set.DefinableMap
  Set.Definable₁

attribute [aesop norm simp (rule_sets := [Definability])]
  imp_iff_not_or
  funext_iff

@[definability]
lemma def_exists_finite {α β : Type*} [Finite β]
    {P : (α → M) → (β → M) → Prop}
    (h : A.Definable L {w : α ⊕ β → M | P (w ∘ Sum.inl) (w ∘ Sum.inr)}) :
    A.Definable L {x : α → M | ∃ a : β → M, P x a} :=
  h.exists_of_finite

@[definability]
lemma def_exists {α : Type*} {P : (α → M) → M → Prop}
    (hp : A.Definable L {w : α ⊕ Fin 1 → M | P (w ∘ Sum.inl) (w (Sum.inr 0))}) :
    A.Definable L {a : α → M | ∃ x : M, P a x} := by
  convert hp.exists_of_finite using 1
  ext a
  simp only [mem_ofPred_eq, Fin.isValue, Sum.elim_comp_inl, Sum.elim]
  constructor
  · intro ⟨x, hx⟩
    use fun _ ↦ x
  · intro ⟨u, hu⟩
    use u 0

@[definability]
lemma def_forall_finite {α β : Type*} [Finite β]
    {P : (α → M) → (β → M) → Prop}
    (h : A.Definable L {w : α ⊕ β → M | P (w ∘ Sum.inl) (w ∘ Sum.inr)}) :
    A.Definable L {x : α → M | ∀ a : β → M, P x a} :=
  h.forall_of_finite

@[definability]
lemma def_forall {α : Type*} {P : (α → M) → M → Prop}
    (hp : A.Definable L {w : α ⊕ Fin 1 → M | P (w ∘ Sum.inl) (w (Sum.inr 0))}) :
    A.Definable L {a : α → M | ∀ x : M, P a x} := by
  convert hp.forall_of_finite using 1
  ext a
  simp only [mem_ofPred_eq, Fin.isValue, Sum.elim_comp_inl, Sum.elim]
  constructor
  · intro h u
    grind
  · intro h x
    exact (imp_iff_right (h fun a ↦ x)).mp fun a ↦ a

@[definability]
lemma def_forall_finite_index {α β : Type*} [Finite β] {P : (α → M) → β → Prop}
    (h : ∀ (i : β), A.Definable L {a : α → M | P a i}) :
    A.Definable L {a : α → M | ∀ (i : β), P a i} := by
  rw [Set.ofPred_forall]
  exact Set.definable_iInter_of_finite h

@[definability]
lemma def_disjunction {α : Type*} {P Q : (α → M) → Prop}
    (hp : A.Definable L {a : α → M | P a}) (hq : A.Definable L {a : α → M | Q a}) :
    A.Definable L {a : α → M | P a ∨ Q a} := hp.union hq

@[definability]
lemma def_conjunction {α : Type*} {P Q : (α → M) → Prop}
    (hp : A.Definable L {a : α → M | P a}) (hq : A.Definable L {a : α → M | Q a}) :
    A.Definable L {a : α → M | P a ∧ Q a} := hp.inter hq

@[definability]
lemma def_negation {α : Type*} {P : (α → M) → Prop}
    (h : A.Definable L {a : α → M | P a}) :
    A.Definable L {a : α → M | ¬ P a} := h.compl

def DefinableFun₁ (L : Language) [L.Structure M] (f : M → M) : Prop :=
  A.DefinableFun L (fun (i : Fin 1 → M) ↦ f (i 0))

@[definability]
lemma definableFun₁_of_graph {f : M → M} (h : A.Definable L {p : Fin 2 → M | f (p 0) = p 1}) :
    A.DefinableFun₁ L f := by
  exact h.preimage_comp fun i : Fin 2 ↦ if i = 0 then some 0 else none

@[definability]
lemma def_comp₁ {α : Type*} {f : M → M} (hf : A.DefinableFun₁ L f)
    {g : (α → M) → M} (hg : A.DefinableFun L g) :
    A.DefinableFun L (fun v ↦ f (g v)) :=
  hf.comp (fun _ ↦ hg)

/-- The image of a Definable set under a DefinableMap is Definable -/
@[definability]
lemma def_image {α β : Type*} [Finite α] [Finite β] {f : (α → M) → (β → M)} {s : Set (α → M)}
    (hs : A.Definable L s) (hf : A.DefinableMap L f) : A.Definable L (f '' s)  := by
  unfold Set.image
  apply def_exists_finite
  refine def_conjunction _ (hs.preimage_map fun i ↦ DefinableFun.proj L) ?_
  simp only [funext_iff]
  apply def_forall_finite_index
  intro i
  exact ((hf i).comp fun j ↦ DefinableFun.proj L).ofPred_eq (DefinableFun.proj L)

@[definability]
lemma def_vecEmpty {α : Type*} : ∀ i, A.Definable L (Matrix.vecEmpty (α := Set (α → M)) i) :=
  fun i ↦ i.elim0

@[definability]
lemma def_vecCons {α : Type*} {s : Set (α → M)} {S : Fin n → Set (α → M)}
    (hs : A.Definable L s) (hS : ∀ i, A.Definable L (S i)) :
    ∀ i, A.Definable L (Matrix.vecCons s S i) :=
  fun i ↦ Fin.cases hs hS i

/-- Concatenating two definable tuples is a definable map. -/
lemma definableMap_append {α : Type*} {n m : ℕ} {f : (α → M) → (Fin n → M)}
    {g : (α → M) → (Fin m → M)}
    (hf : Set.univ.DefinableMap L f) (hg : Set.univ.DefinableMap L g) :
    Set.univ.DefinableMap L (fun v ↦ Fin.append (f v) (g v)) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [Fin.append_left]; exact hf j
  · intro j; simp only [Fin.append_right]; exact hg j

@[definability]
lemma definableFun_const_univ {α : Type*} (c : M) :
  Set.univ.DefinableFun L (fun _ : α → M ↦ c) := definableFun_const L α (mem_univ c)

@[definability]
lemma def_preimage_comp {α β : Type*} {A : Set M} {s : Set (β → M)}
    (h : A.Definable L s) (f : β → α) :
    A.Definable L {v : α → M | v ∘ f ∈ s} := by
  apply h.preimage_comp

@[definability]
lemma def_pair_mem {α : Type*} {s : Set (Fin 2 → M)} (hs : Set.univ.Definable L s)
    {f g : (α → M) → M} (h1 : Set.univ.DefinableFun L f) (h2 : Set.univ.DefinableFun L g) :
    Set.univ.Definable L {v : α → M | ![f v, g v] ∈ s} :=
  hs.preimage_map (fun i ↦ by fin_cases i <;> assumption)

@[aesop unsafe 10% apply (rule_sets := [Definability])]
lemma def_rel_pair {α : Type*} {R : M → M → Prop}
    (hR : Set.univ.Definable L {v : Fin 2 → M | R (v 0) (v 1)})
    {g1 g2 : (α → M) → M}
    (h1 : Set.univ.DefinableFun L g1) (h2 : Set.univ.DefinableFun L g2) :
    Set.univ.Definable L {a : α → M | R (g1 a) (g2 a)} := by
  have h : {a : α → M | R (g1 a) (g2 a)}
      = (fun a : α → M ↦ ![g1 a, g2 a]) ⁻¹' {v : Fin 2 → M | R (v 0) (v 1)} := by
    ext a; simp
  rw [h]
  refine hR.preimage_map (fun i ↦ ?_)
  fin_cases i <;> definability

@[definability]
lemma def_snoc_mem {α : Type*} {m : ℕ} {s : Set (Fin (m + 1) → M)}
    (hs : Set.univ.Definable L s)
    {f : (α → M) → (Fin m → M)} (hf : Set.univ.DefinableMap L f)
    {g : (α → M) → M} (hg : Set.univ.DefinableFun L g) :
    Set.univ.Definable L {v : α → M | Fin.snoc (f v) (g v) ∈ s} :=
  hs.preimage_map (fun i ↦ Fin.lastCases (by simpa using hg) (fun j ↦ by simpa using hf j) i)

@[aesop norm forward (rule_sets := [Definability])]
lemma def_finite {s : Set M} (hs : s.Finite) : Set.univ.Definable₁ L s := by
  unfold Set.Definable₁
  have h : {x : Fin 1 → M | x 0 ∈ s}
      = ⋃ a ∈ hs.toFinset, {x : Fin 1 → M | x 0 ∈ ({a} : Set M)} := by
    ext x; simp
  rw [h]
  exact Set.definable_biUnion_finset
    (fun a ↦ Set.Definable.singleton_of_mem L (Set.mem_univ a)) _

end Set

namespace TameGeometry

variable {N : Type*} [L.Structure N]

/-- A family $(Y_x)_{x ∈ M}$ of subsets of $M^n$ is called definable if
  ${(x,y) | y ∈ Y_x }$ is definable -/
def def_family_univ (L : Language) [L.Structure N] {m : ℕ} (f : N → Set (Fin m → N)) : Prop :=
  Set.univ.Definable L {n : Fin (m + 1) → N | Fin.tail n ∈ f (n 0)}

/-- A family $(Y_x)_{x ∈ M}$ of subsets of $M$ is called definable if
  ${(x,y) | y ∈ Y_x }$ is definable -/
def def_family_univ₁ (L : Language) [L.Structure N] (f : N → Set N) : Prop :=
  Set.univ.Definable L {n : Fin 2 → N | n 1 ∈ f (n 0)}

/-- A family $(Y_p)$ of subsets of $M$ indexed by tuples $p : α → M$ is
  called definable if ${(p, y) | y ∈ Y_p}$ is definable -/
def def_family₁ (L : Language) [L.Structure N] {α : Type*} (s : (α → N) → Set N) : Prop :=
  Set.univ.Definable L {v : α ⊕ Fin 1 → N | v (Sum.inr 0) ∈ s (v ∘ Sum.inl)}

lemma def_family_univ_iff (f : N → Set N) :
  def_family_univ₁ L f ↔ def_family_univ L (fun x ↦ {v : Fin 1 → N | v 0 ∈ f x}) := by rfl

attribute [aesop norm unfold (rule_sets := [Definability])]
  def_family_univ def_family_univ₁ def_family₁

@[aesop unsafe 20% apply (rule_sets := [Definability])]
lemma def_family_univ_mem {α : Type*} {n : ℕ} {f : N → Set (Fin n → N)}
    (h : def_family_univ L f) {G : (α → N) → (Fin n → N)} (hG : Set.univ.DefinableMap L G)
    {g : (α → N) → N} (hg : Set.univ.DefinableFun L g) :
    Set.univ.Definable L {v : α → N | G v ∈ f (g v)} :=
  h.preimage_map (F := fun v ↦ Fin.cons (g v) (G v)) (Fin.cases hg hG)

/-- Each fibre of a definable family is definable -/
lemma def_family_fiber {n : ℕ} {f : N → Set (Fin n → N)} (h : def_family_univ L f) (x : N) :
    Set.univ.Definable L (f x) := by
  refine h.preimage_map (F := fun v : Fin n → N ↦ Fin.cons x v) (fun i ↦ ?_)
  refine Fin.cases ?_ ?_ i
  · exact Set.definableFun_const_univ x
  · exact fun j ↦ Set.DefinableFun.proj L

lemma def_family_fiber_univ₁ {S : N → Set N} (h : def_family_univ₁ L S) (x : N) :
    Set.univ.Definable₁ L (S x) := by
  exact def_family_fiber ((def_family_univ_iff S).mp h) x

/-- Projecting each fiber of a definable family to its first coordinate -/
lemma def_family_proj₀ {n : ℕ} {f : N → Set (Fin (n + 1) → N)}
    (h : def_family_univ L f) :
    def_family_univ₁ L (fun x ↦ (· 0) '' f x) := by
  definability

/-- fixing the first coordinate of each fiber -/
lemma def_family_fixed
    {n : ℕ} {f : N → Set (Fin (n + 1) → N)} (h : def_family_univ L f) (c : N) :
    def_family_univ L (fun x ↦ {v ∈ f x | v 0 = c}) := by
  definability

lemma def_family_tail {n : ℕ} {f : N → Set (Fin (n + 1) → N)} (h : def_family_univ L f) :
  def_family_univ L (fun x ↦ Fin.tail '' f x) := by definability

lemma def_family_preimage_cons {n : ℕ} {f : N → Set (Fin (n + 1) → N)}
    (h : def_family_univ L f) (a : N) :
    def_family_univ L (fun x ↦ (Fin.cons (α := fun _ ↦ N) a) ⁻¹' f x) := by
  have h1 : ∀ x, Fin.tail '' {v ∈ f x | v 0 = a} = (Fin.cons (α := fun _ ↦ N) a) ⁻¹' f x := by
    intro x
    ext w
    simp only [Set.mem_image, Set.mem_sep_iff, Set.mem_preimage]
    constructor
    · intro hw
      obtain ⟨v, ⟨hv, hva⟩, hvw⟩ := hw
      rw [← hvw, ← hva, Fin.cons_self_tail]
      exact hv
    · exact fun hc ↦ ⟨Fin.cons a w, ⟨hc, by simp⟩, by simp⟩
  have h2 := def_family_tail (def_family_fixed h a)
  rw [funext h1] at h2
  exact h2

lemma def_fiber_left {s : Set (Fin 2 → N)} (hs : Set.univ.Definable L s) (a : N) :
    Set.univ.Definable₁ L {y | ![a, y] ∈ s} := by
  change Set.univ.Definable L {v : Fin 1 → N | ![a, v 0] ∈ s}
  have h1 : {v : Fin 1 → N | ![a, v 0] ∈ s}
    = (fun v : Fin 1 → N ↦ ![a, v 0]) ⁻¹' s := by rfl
  rw [h1]
  refine Set.Definable.preimage_map (fun i ↦ ?_) hs
  fin_cases i
  · exact Set.definableFun_const_univ a
  · exact Set.DefinableFun.proj L

lemma def_family_fiber' {α : Type*} [Finite α]
    {S : (α → N) → Set N} (h : def_family₁ L S)
    (p : α → N) : Set.univ.Definable₁ L (S p) := by
  change Set.univ.Definable L {x : Fin 1 → N | x 0 ∈ S p}
  refine Set.Definable.preimage_map (F := fun x : Fin 1 → N ↦ Sum.elim p x) ?_ h
  intro i
  cases i with
  | _ => definability

variable [L.IsOrdered] [LinearOrder N] [L.OrderedStructure N]

/-- For definable n-ary functions f and g the set {v | f v < g v} is definable -/
@[definability]
lemma setOf_lt {α : Type*} {f g : (α → N) → N} {A : Set N}
    (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.Definable L {v : α → N | f v < g v} := by
  have h1 : A.DefinableMap L (fun v ↦ ![f v, g v]) := by
    simp [Set.DefinableMap, *]
  have h2 : (∅ : Set N).Definable L {p : Fin 2 → N | p 0 < p 1} := by
    rw [Set.empty_definable_iff]
    let φ : L.Formula (Fin 2) := (Term.var (Sum.inl 0)).lt (Term.var (Sum.inl 1))
    use φ
    ext p
    simp only [Fin.isValue, Set.mem_ofPred_eq]
    rw [← FirstOrder.Language.Formula.boundedFormula_realize_eq_realize φ p]
    rw [Term.realize_lt]
    · simp
    · exact fun a ↦ a.elim0
  exact (h2.mono (Set.empty_subset A)).preimage_map h1

/-- For definable n-ary functions f and g the set {v | f v ≤ g v} is definable -/
@[definability]
lemma setOf_le {α : Type*} {f g : (α → N) → N} {A : Set N}
    (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.Definable L {v : α → N | f v ≤ g v} := by
  simpa [Set.compl_ofPred] using (setOf_lt hg hf).compl

/-- range of fiber minimum of a definable family is definable. -/
lemma def_family_least_range {f : N → Set N} (h : def_family_univ₁ L f) {g : N → N}
    (hg : ∀ x, IsLeast (f x) (g x)) : Set.univ.Definable₁ L (Set.range g) := by
  have h1 : Set.range g = {y | ∃ x, IsLeast (f x) y} := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := hy
      refine ⟨x, ?_⟩
      rw [← hx]
      exact hg x
    · intro hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, ((hg x).isLeast_iff_eq).mp hx⟩
  rw [h1]
  definability

lemma def_family_lub_univ₁ {s : N → Set N} (h : def_family_univ₁ L s) :
    Set.univ.Definable L {w : Fin 2 → N | IsLUB (s (w 0)) (w 1)} := by
  definability

end TameGeometry

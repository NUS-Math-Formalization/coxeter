import Mathlib.Order.UpperLower.Hom
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice

/--
An abstract simplicial complex is a pair (V,F) where V is a set and F is a set of finite subsets of V such that
  (1) ∅ ∈ F,
  (2) if s ∈ F and t ⊆ s, then t ∈ F.
-/
@[ext]
structure AbstractSimplicialComplex (V : Type*)  where
  faces : Set (Finset V) -- the set of faces
  empty_mem : ∅ ∈ faces
  lower' : IsLowerSet faces -- The set of faces is a lower set under the inclusion relation.

theorem AbstractSimplicialComplex.nonempty {V : Type*} {F : AbstractSimplicialComplex V} : F.faces.Nonempty := Set.nonempty_of_mem F.empty_mem

theorem isLowerSet_singleton_empty (α : Type*):
IsLowerSet {(∅ : Set α)} := by
  intro _ _ blea ain
  rw [ain, ← Set.bot_eq_empty, ← eq_bot_iff, Set.bot_eq_empty] at blea
  rw [blea]; rfl

theorem Finset.isLowerSet_singleton_empty (α : Type*):
IsLowerSet {(∅ : Finset α)} := by
  intro _ _ blea ain
  rw [ain, ← Finset.bot_eq_empty, ← eq_bot_iff, Finset.bot_eq_empty] at blea
  rw [blea]; rfl

open Classical

namespace AbstractSimplicialComplex

variable {V : Type*}

lemma subset_mem (F : AbstractSimplicialComplex V) : ∀ {s t}, s ∈ F.faces →  t ⊆ s → t ∈ F.faces
  := fun hs hst => F.lower' hst hs

instance : SetLike (AbstractSimplicialComplex V) (Finset V) where
  coe F := F.faces
  coe_injective' p q h := by
    obtain ⟨_, _⟩ := p
    obtain ⟨_, _⟩ := q
    congr

@[simp, nolint simpNF]
theorem mem_faces {F : AbstractSimplicialComplex V} : x ∈ F.faces ↔ x ∈ F :=
  Iff.rfl

lemma eq_iff_faces (F G : AbstractSimplicialComplex V) : F = G ↔ F.faces = G.faces := by
  constructor <;> (intro h; ext; rw [h])

/--
The rank of an ASC is defined to be the supremum of the cardinals of its faces.
If the size of simplices in F is unbounded, it has rank `0` by definition.

Remark: We should general be careful with the unbounded case.
-/
noncomputable def rank (F : AbstractSimplicialComplex V) : ℕ := iSup fun s : F.faces => s.1.card

/-- Definition: For any ASC `F`, we denote by `vertices F` the set of vertices of F. -/
def vertices (F : AbstractSimplicialComplex V) : Set V := ⋃ s : F.faces, s.1.toSet

/--
Definition: The simplex with verteces `s ⊆ V` is the complex of all finite subsets of `s`.
-/
def simplex (s : Set V) : AbstractSimplicialComplex V where
  faces := {t | t.toSet ⊆ s}
  empty_mem := by simp
  lower' := by
    intro a b h1 h2
    refine' Set.Subset.trans ?_ h2
    congr

section order

@[simp]
def le (G F : AbstractSimplicialComplex V) := G.faces ⊆ F.faces

/--
The set of all ASC over V admits a partial ordering by inclusion of the set of faces. We denote this relation by G ≤ F.
-/
instance partialOrder : PartialOrder (AbstractSimplicialComplex V) where
  le := le
  le_refl := fun _ => by simp only [le, refl]
  le_trans := fun _ _ _ => by simp only [le]; exact Set.Subset.trans
  le_antisymm := fun G F => by
    simp only [le]
    intro h1 h2
    exact SetLike.ext' <| Set.Subset.antisymm h1 h2

@[simp]
lemma le_def {G F : AbstractSimplicialComplex V} : G ≤ F ↔ G.faces ⊆ F.faces := by rfl

@[simp]
lemma simplex_face {s : Set V} {a : Finset V} : a ∈ (simplex s).faces ↔ a.toSet ⊆ s := by rfl

instance inf_set : InfSet (AbstractSimplicialComplex V) where
  sInf := fun s => ⟨⋂ F : s, F.1.faces,
    Set.mem_iInter.mpr (fun F => F.1.empty_mem),
    isLowerSet_iInter (fun F => F.1.lower')⟩

@[simp]
lemma sInf_def (s : Set (AbstractSimplicialComplex V)) : (sInf s).faces = ⋂ F : s, F.1.faces := rfl

lemma sInf_isGLB (s : Set (AbstractSimplicialComplex V)) : IsGLB s (sInf s) := by
  constructor
  . intro x hx
    refine Set.iInter_subset_of_subset ⟨x, hx⟩ ?_
    simp only [subset_of_eq]
  . intro x hx
    simp_rw [mem_lowerBounds,le_def] at hx
    rw [le_def, sInf_def]
    simp only [Set.subset_iInter_iff, Subtype.coe_prop, hx, Subtype.forall, implies_true, forall_const]


/-- instance: The set of all ASCs on `V` is a complete lattice with intersections and unions of the set of faces.
-/
instance instCompleteLatticeToAbstractSimplicialComplex : CompleteLattice (AbstractSimplicialComplex V)
where
  inf := fun F G => ⟨F.faces ∩ G.faces, Set.mem_inter F.empty_mem G.empty_mem, IsLowerSet.inter F.lower' G.lower'⟩
  le_inf := fun _ _ _ hab hac _ ha =>
    Set.mem_inter (hab ha) (hac ha)
  inf_le_right := fun _ _ _ ha =>
      ha.2
  inf_le_left := fun _ _ _ ha => ha.1
  __ := completeLatticeOfInf (AbstractSimplicialComplex V) sInf_isGLB

@[simp]
lemma inf_faces (F G : AbstractSimplicialComplex V) : (F ⊓ G).faces = F.faces ∩ G.faces := rfl

def unionSubset {s : Set <| AbstractSimplicialComplex V} (hs : s.Nonempty) : AbstractSimplicialComplex V where
  faces := ⋃ F : s, F.1.faces
  empty_mem := by
    simp [Set.mem_iUnion]
    rcases hs with ⟨e, he⟩
    exact ⟨e, he, e.empty_mem⟩
  lower' := isLowerSet_iUnion fun i ↦ i.1.lower'

lemma sSup_eq_unionSubset {s : Set <| AbstractSimplicialComplex V} (hs : s.Nonempty) : sSup s = unionSubset hs := by
  apply le_antisymm
  · apply sSup_le
    intro b bs
    rw [le_def, show (unionSubset hs).faces = ⋃ F : s, F.1.faces by rfl]
    apply Set.subset_iUnion_of_subset ⟨b, bs⟩
    simp only [subset_of_eq]
  · rw [le_sSup_iff]
    exact fun _ hb ↦ Set.iUnion_subset fun i ↦ hb i.2


@[simp]
lemma sSup_faces_of_nonempty {s : Set (AbstractSimplicialComplex V)} (h : s.Nonempty) : (sSup s).faces = ⋃ F : s, F.1.faces := by
  rw [sSup_eq_unionSubset h]; rfl

@[simp]
lemma sup_faces (F G : AbstractSimplicialComplex V) : (F ⊔ G).faces = F.faces ∪ G.faces := by
  let s : Set (AbstractSimplicialComplex V) := {F, G}
  rw [show F ⊔ G = sSup s by simp [s], show F.faces ∪ G.faces = ⋃ i : s, i.1.faces by simp [s], sSup_faces_of_nonempty (by simp [s])]

@[simp]
theorem iInf_faces {ι : Type*} (x : ι → AbstractSimplicialComplex V) : (⨅ i, x i).faces = ⋂ i, (x i).faces := by
  unfold iInf
  simp only [sInf_def, Set.iInter_coe_set, Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq',
    Set.sInf_eq_sInter, Set.sInter_range]

@[simp]
theorem iSup_faces_of_nonempty {ι : Type*} (x : ι → AbstractSimplicialComplex V) [Nonempty ι] : (⨆ i, x i).faces = ⋃ i, (x i).faces := by
  unfold iSup
  rw [sSup_faces_of_nonempty]
  · simp
  · by_contra h
    apply Set.not_nonempty_iff_eq_empty.1 at h
    simp at h

end order

section closure

/-- Definition: For a collection s of subsets of V, we denote by closure s the smallest ASC over V containing all elements in s
as faces.

Remark: Here we secretly consider the ambient space as the simplex with vertex set V.

Maybe don't use `abbrev` will be better? Because sometimes we don't want `simp` to expand this construction.
-/
abbrev closure (s : Set (Finset V))
  : AbstractSimplicialComplex V := sInf {K | s ⊆  K.faces}

lemma subset_closure_faces (s : Set (Finset V)) : s ⊆ (closure s).faces := by
  simp only [sInf_def, Set.coe_setOf, Set.mem_setOf_eq, Set.subset_iInter_iff, Subtype.forall,
    imp_self, forall_const]

lemma closure_faces_eq_self (F : AbstractSimplicialComplex V) : closure F.faces = F := by
  apply le_antisymm
  · apply sInf_le; simp only [Set.mem_setOf_eq]; rfl
  · simp only [le_sInf_iff, Set.mem_setOf_eq, le_def, imp_self, forall_const]

lemma closure_mono {s t: Set (Finset V)} : s ⊆ t → closure s ≤ closure t := by
  intro hst
  apply sInf_le_sInf
  rw [Set.setOf_subset_setOf]
  intro _ h; exact Set.Subset.trans hst h

/-- Lemma: For a `f : Finset V`, the closure of `{f}` is the simplex of `f`.-/
lemma closure_simplex (f : Finset V) : closure {f} =  simplex f := by
  have h1 : (closure {f}).faces = (simplex f).faces:= by
    apply Set.Subset.antisymm <;> rw [sInf_def]
    · rintro s h1
      simp only [Set.singleton_subset_iff, mem_faces, Set.mem_setOf_eq, Set.mem_iInter, Set.coe_setOf, Subtype.forall] at h1
      exact h1 (simplex ↑f) fun ⦃_⦄ a => a
    · rintro s h1
      apply simplex_face.1 at h1
      simp only [Finset.coe_subset] at h1
      simp only [Set.singleton_subset_iff, mem_faces, Set.mem_setOf_eq, Set.mem_iInter, Set.coe_setOf, Subtype.forall]
      intro i fi
      apply mem_faces.1 <| i.lower' h1 <| mem_faces.2 fi
  exact instSetLikeAbstractSimplicialComplexFinset.proof_1 (closure {f}) (simplex ↑f) h1

/-- Explicit construction of `closure s` for `s : Set (Finset V)`-/
def closurePower (s : Set (Finset V)) : AbstractSimplicialComplex V where
  faces :=
    if Nonempty s then
      ⋃ f : s, {t | t ⊆ f}
    else
      {∅}
  empty_mem := by
    by_cases h : Nonempty s <;> simp [h]
    exact nonempty_subtype.mp h
  lower' := by
    by_cases h : Nonempty s <;> simp [h]
    · refine isLowerSet_iUnion₂ ?_
      intro t _ a b h1 h2
      refine' Set.Subset.trans ?_ h2
      congr
    · exact Finset.isLowerSet_singleton_empty V

/-- Similar statement for `⨅` is not true.-/
theorem closure_iUnion_eq_iSup_closure {ι : Type*} (p : ι → Set (Finset V)) :
  closure (⋃ i : ι, p i) = ⨆ i : ι, closure (p i) := by
  apply le_antisymm
  · apply sInf_le
    simp only [Set.iUnion_subset_iff, Set.mem_setOf_eq]
    intro i
    apply subset_trans <| subset_closure_faces <| p i
    rw [← le_def]
    apply le_iSup (fun i ↦ closure (p i)) i
  · apply iSup_le
    intro i
    apply closure_mono <| Set.subset_iUnion p i

/--
Lemma: Let `s` be a collection of finsets in `V`. Then the closure of `s` is just the union of the closure of elements in `s`.

Remark: So taking closure commuts with taking union.
-/
lemma closure_eq_iSup (s : Set (Finset V)) : closure s = ⨆ f : s,  closure {f.1} := by
  rw [← closure_iUnion_eq_iSup_closure,
    Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype, Set.setOf_mem_eq]

theorem closure_eq_closurePower (s: Set (Finset V)) : closure s = closurePower s := by
  ext t
  constructor <;> intro ts
  · simp only [sInf_def, Set.coe_setOf, Set.mem_setOf_eq, Set.mem_iInter, mem_faces,
    Subtype.forall] at ts
    unfold closurePower
    apply ts
    by_cases h : Nonempty s <;> simp [h]
    · rw [Set.subset_def]
      intro x xs
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      use x
    · simp at h
      apply Set.eq_empty_of_forall_not_mem at h
      intro g hg
      rw [h] at hg
      contradiction
  · rw [closurePower] at ts
    by_cases h : Nonempty s <;> simp [h]
    · simp [closurePower,h] at ts
      intro K sK
      obtain ⟨f,fs⟩ := ts
      rw [Set.subset_def] at sK
      obtain ⟨fs, tf⟩ := fs
      apply sK at fs
      exact mem_faces.1 <| K.lower' tf <| fs
    · simp [closurePower, h] at ts
      intro K _
      apply mem_faces.1
      rw [ts]
      exact K.empty_mem

lemma closure_faces (s : Set (Finset V)) : (closure s).faces = if Nonempty s then ⋃ f : s, {t : Finset V | t ⊆ f} else {∅} := by
  rw [closure_eq_closurePower]; rfl

lemma closure_singleton_faces (f : Finset V) : (closure {f}).faces = {t : Finset V | t ⊆ f} := by
  rw [closure_faces]
  simp only [nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceIte, Set.iUnion_coe_set,
    Set.iUnion_iUnion_eq_left]

instance instNonemptyToAbstractSimplicialComplexContainingSet (s : Set (Finset V)) : Nonempty {x : AbstractSimplicialComplex V // s ⊆ x.faces} := ⟨closure s, subset_closure_faces _⟩

/--
Lemma: Let F be an ASC. Then the closure of the set of faces is just F.
-/
lemma closure_self {F : AbstractSimplicialComplex V} : closure (F.faces) = F := by
  have h1 : (closure (F.faces)).faces = F.faces:= by
    apply Set.Subset.antisymm
    · rw [sInf_def]
      rintro s h1; simp only [Set.mem_setOf_eq, Set.mem_iInter, mem_faces, Set.coe_setOf, Subtype.forall] at h1
      exact h1 F fun ⦃_⦄ a => a
    · rw [sInf_def]
      rintro s h1; simp only [Set.mem_setOf_eq, Set.mem_iInter, mem_faces, Set.coe_setOf, Subtype.forall]
      exact fun _ i => i h1
  exact instSetLikeAbstractSimplicialComplexFinset.proof_1 (closure F.faces) F h1

lemma closure_le {F : AbstractSimplicialComplex V} (h: s ⊆ F.faces) : closure s ≤ F := by
  rintro s2 h2
  simp only [sInf_def, Set.mem_setOf_eq, Set.mem_iInter, mem_faces, Set.coe_setOf, Subtype.forall] at h2
  exact h2 F h

instance instCompleteDistribLatticeToAbstractSimplicialComplex : CompleteDistribLattice (AbstractSimplicialComplex V) := {
  instCompleteLatticeToAbstractSimplicialComplex with
  inf_sSup_le_iSup_inf := by
    intro a s
    by_cases hs : s.Nonempty
    · simp [hs, Set.inter_iUnion]
      intro i is f hf
      rw [Set.mem_iUnion]
      use i
      simp only [is, iSup_pos, inf_faces, hf]
    · simp only [Set.not_nonempty_iff_eq_empty.mp hs, sSup_empty, ge_iff_le, bot_le,
      inf_of_le_right, Set.mem_empty_iff_false, not_false_eq_true, iSup_neg, iSup_bot, le_refl]
  iInf_sup_le_sup_sInf := by
    intro a s
    simp only [le_def, iInf_faces, sup_faces, sInf_def, Set.iInter_coe_set, Set.union_iInter,
      Set.subset_iInter_iff]
    intro i is f hf
    rw [Set.mem_iInter] at hf
    replace hf := hf i
    simp only [is, iInf_pos, sup_faces, Set.mem_union, mem_faces] at hf
    simp only [Set.mem_union, mem_faces, hf]
}

end closure

section facet_and_pure

/--
Definition: Let `F` be an ASC. A maximal face of F is called a facet of F.
-/
def IsFacet (F : AbstractSimplicialComplex V) (s : Finset V) := s ∈ F ∧ ∀ t ∈ F, s ⊆ t → s = t

/--
Definition: For any ASC F, we denote by Facets F the set of facets of F.
-/
def Facets (F : AbstractSimplicialComplex V) : Set (Finset V) := {s | F.IsFacet s}

/-- Definition: A pure abstract simplicial complex is an abstract simplicial complex
    where all facets have the same cardinality. -/
def IsPure (F : AbstractSimplicialComplex V) :=
  ∀ s ∈ Facets F, ∀ t ∈ Facets F, s.card = t.card

@[deprecated IsPure]
class Pure (F : AbstractSimplicialComplex V) : Prop where
  pure : ∀ s ∈ F.Facets, ∀ t ∈ F.Facets, s.card = t.card

/--Definition: We will call an ASC pure of rank `d` if all its facets has `d` elements-/
def IsPure' (F : AbstractSimplicialComplex V) (d : ℕ) :=
  ∀ s ∈ F.Facets, s.card = d

@[deprecated IsPure']
class Pure' (F : AbstractSimplicialComplex V) (d : ℕ) : Prop where
  pure : ∀ s ∈ F.Facets, s.card = d

/-- The definitions of purity are equivalent. -/
lemma isPure_iff_isPure' {F : AbstractSimplicialComplex V} : F.IsPure ↔ ∃ d, F.IsPure' d := by
  by_cases hemp : Nonempty F.Facets
  · constructor
    · let s := Classical.choice (hemp)
      exact fun hIp ↦ ⟨s.1.card, fun t ht ↦ hIp t ht s s.2⟩
    · rintro ⟨d, hIp'⟩ s hs t ht
      rw [hIp' s hs, hIp' t ht]
  · constructor
    · intro; use 0
      simp only [IsPure', Finset.card_eq_zero]
      contrapose! hemp
      rcases hemp with ⟨d, ⟨_, _⟩⟩
      use d
    · intro
      simp only [nonempty_subtype, not_exists] at hemp
      intro s hs
      exfalso
      exact hemp s hs

/-- The simplex of `f : Finset V` contains a unique facet `f`.-/
@[simp]
theorem closure_singleton_Facets (f : Finset V) : (closure {f}).Facets = {f} := by
  ext g; constructor <;> intro hg
  · rcases hg with ⟨hg_mem, hg_max⟩
    rw [Set.mem_singleton_iff]
    contrapose! hg_max
    use f; constructor
    · apply mem_faces.mp
      apply Set.mem_of_subset_of_mem <| subset_closure_faces {f}
      rfl
    · refine ⟨?_, hg_max⟩
      rw [← mem_faces, closure_faces] at hg_mem
      simpa only [nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceIte,
        Set.iUnion_coe_set, Set.iUnion_iUnion_eq_left, Set.mem_setOf_eq] using hg_mem
  · rw [Set.mem_singleton_iff] at hg
    subst hg; constructor
    · apply Set.mem_of_subset_of_mem <| subset_closure_faces {g}; rfl
    · intro t ht
      rw [← mem_faces, closure_faces] at ht
      simp only [nonempty_subtype, Set.mem_singleton_iff, exists_eq, ↓reduceIte, Set.iUnion_coe_set,
        Set.iUnion_iUnion_eq_left, Set.mem_setOf_eq] at ht
      apply fun h ↦ subset_antisymm h ht

/-- Simplexes of finsets are pure. -/
theorem isPure_closure_singelton (f : Finset V) : IsPure (closure {f}) := by
  intro s hs t ht
  rw [closure_singleton_Facets, Set.mem_singleton_iff] at *
  rw [hs, ht]

/-- The simplex of `f ∩ g` with `f g : Finset V` is equal to the infimum of the simplexes of `f` and `g`. -/
theorem closure_singleton_inter_eq_inf {f g : Finset V} : closure {f ∩ g} = closure {f} ⊓ closure {g} := by
  simp only [eq_iff_faces, inf_faces, closure_singleton_faces]
  ext x; constructor <;> {
    intro h
    simpa only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.subset_inter_iff] using h
  }

lemma bot_eq_closurePower_empty : (⊥ : AbstractSimplicialComplex V) = closurePower ∅ := by
  symm
  rw [eq_bot_iff, le_def, show (closurePower ∅).faces = {∅} by simp[closurePower], Set.singleton_subset_iff]
  apply (⊥ : AbstractSimplicialComplex V).empty_mem

lemma bot_eq_closure_empty : (⊥ : AbstractSimplicialComplex V) = closure ∅ := by
  symm
  rw [closure_eq_closurePower]
  rw [eq_bot_iff, le_def, show (closurePower ∅).faces = {∅} by simp[closurePower], Set.singleton_subset_iff]
  apply (⊥ : AbstractSimplicialComplex V).empty_mem

/-- The bottom of ASC is the singleton of emptyset. -/
@[simp]
lemma bot_faces_eq_empty : (⊥ : AbstractSimplicialComplex V).faces = {∅} := by
  rw [bot_eq_closurePower_empty]
  simp only [closurePower, nonempty_subtype, Set.mem_empty_iff_false, exists_const, ↓reduceIte]

@[simp]
theorem bot_Facets : (⊥ : AbstractSimplicialComplex V).Facets = {∅} := by
  ext x; constructor <;> intro hx
  · rw [← bot_faces_eq_empty, mem_faces]
    exact hx.1
  · rw [Set.mem_singleton_iff.mp hx]
    refine ⟨(⊥ : AbstractSimplicialComplex V).empty_mem, ?_⟩
    intro t ht _
    rw [← mem_faces, bot_faces_eq_empty, Set.mem_singleton_iff] at ht
    exact ht.symm

@[simp]
theorem isPure_bot : IsPure (⊥ : AbstractSimplicialComplex V) := by
  intro s hs t ht
  rw [bot_Facets, Set.mem_singleton_iff] at *
  rw [hs, ht]

@[simp]
theorem iSup_faces_of_isEmpty {ι : Type*} [IsEmpty ι] (x : ι → AbstractSimplicialComplex V) : (⨆ i, x i).faces = {∅} := by
  simp only [iSup_of_empty, bot_faces_eq_empty]

/-- Given a nonempty family `p i` of ASCs, every facet of their supremum `⨆ i, p i` is a facet of some `p i`. -/
theorem iSup_Facets_le_of_nonempty {ι : Type*} [Nonempty ι] {p : ι → AbstractSimplicialComplex V} : (⨆ i : ι, p i).Facets ≤ ⋃ i : ι, (p i).Facets := by
  intro a ha
  rw [Set.mem_iUnion]
  rcases ha with ⟨ha_mem, ha_max⟩
  rw [← mem_faces, iSup_faces_of_nonempty, Set.mem_iUnion] at ha_mem
  rcases ha_mem with ⟨i, hi⟩
  use i
  constructor
  · exact mem_faces.mpr hi
  · intro t ht
    apply ha_max
    rw [← mem_faces, iSup_faces_of_nonempty]
    apply Set.mem_iUnion_of_mem i ht

lemma exits_mem_faces_of_mem_iSup {ι : Type*} [Nonempty ι] {p : ι → AbstractSimplicialComplex V}  (hf : f ∈ (⨆ i : ι, p i).Facets) : ∃ i : ι, f ∈ (p i).Facets :=
  Set.mem_iUnion.mp (iSup_Facets_le_of_nonempty hf)

/-- The supremum of a nonempty pure ASC family is pure. -/
theorem isPure_iSup_isPure {ι : Type*} [Nonempty ι] {p : ι → AbstractSimplicialComplex V} {d : ℕ} (hp : ∀i : ι, IsPure' (p i) d) : IsPure' (⨆ i : ι, p i) d := by
  intro s hs
  obtain ⟨i, hi⟩ := exits_mem_faces_of_mem_iSup hs
  apply hp i s hi

end facet_and_pure

end AbstractSimplicialComplex

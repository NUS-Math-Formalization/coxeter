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
theorem mem_faces {F : AbstractSimplicialComplex V} {x : Finset V} : x ∈ F.faces ↔ x ∈ F :=
  Iff.rfl

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

/--
Definition: The simplex with verteces s ⊆ V is the complex of all finite subsets of s.
-/
def simplex (s : Set V) : AbstractSimplicialComplex V where
  faces := {t | t.toSet ⊆ s}
  empty_mem := by simp
  lower' := by
    intro a b h1 h2
    refine' Set.Subset.trans ?_ h2
    congr

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
    rw [le_def,sInf_def]
    simp only [Set.subset_iInter_iff, Subtype.coe_prop, hx, Subtype.forall, implies_true, forall_const]


/-- instance: The set of all ASCs on V is a complete lattice with intersections and unions of the set of faces.
-/
instance complete_lattice : CompleteLattice (AbstractSimplicialComplex V)
where
  inf := fun F G => ⟨F.faces ∩ G.faces, Set.mem_inter F.empty_mem G.empty_mem, IsLowerSet.inter F.lower' G.lower'⟩
  le_inf := fun _ _ _ hab hac _ ha =>
    Set.mem_inter (hab ha) (hac ha)
  inf_le_right := fun _ _ _ ha =>
      ha.2
  inf_le_left := fun _ _ _ ha => ha.1
  __ := completeLatticeOfInf (AbstractSimplicialComplex V) sInf_isGLB

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

def ofEmpty : AbstractSimplicialComplex V where
  faces := {∅}
  empty_mem := rfl
  lower' := Finset.isLowerSet_singleton_empty V

lemma bot_eq_ofEmpty : (⊥ : AbstractSimplicialComplex V) = ofEmpty := by
  symm
  rw [eq_bot_iff, le_def, show ofEmpty.faces = {∅} by rfl, Set.singleton_subset_iff]
  apply (⊥ : AbstractSimplicialComplex V).empty_mem

lemma bot_faces_eq_empty : (⊥ : AbstractSimplicialComplex V).faces = {∅} := by
  rw [bot_eq_ofEmpty]; rfl

@[simp]
lemma sSup_faces_of_nonempty {s : Set (AbstractSimplicialComplex V)} (h : s.Nonempty) : (sSup s).faces = ⋃ F : s, F.1.faces := by
  rw [sSup_eq_unionSubset h]; rfl

/--
Definition: For any ASC F, we denote by vertices F the set of vertices of F.
-/
def vertices (F : AbstractSimplicialComplex V) : Set V := ⋃ s : F.faces, s.1.toSet

/--
Definition: Let F be an ASC. A maximal face of F is called a facet of F.
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

class Pure (F : AbstractSimplicialComplex V) : Prop where
  pure : ∀ s ∈ F.Facets, ∀ t ∈ F.Facets, s.card = t.card

/--Definition: We will call an ASC pure of rank `d` if all its facets has `d` elements-/
def IsPure' (F : AbstractSimplicialComplex V) (d : ℕ) :=
  ∀ s ∈ F.Facets, s.card = d

class Pure' (F : AbstractSimplicialComplex V) (d : ℕ) : Prop where
  pure : ∀ s ∈ F.Facets, s.card = d

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
      intro s hs t _
      exfalso
      exact hemp s hs

lemma pure_def {F : AbstractSimplicialComplex V} [Pure F] : ∀ s ∈ F.Facets, ∀ t ∈ F.Facets, s.card = t.card := Pure.pure

lemma pure_isPure {F : AbstractSimplicialComplex V} [Pure F] : IsPure F := pure_def

/--
If the size of simplices in F is unbounded, it has rank 0 by definition.

Remark: We should general be careful with the unbounded case.
-/

noncomputable def rank (F : AbstractSimplicialComplex V) : ℕ := iSup fun s : F.faces => s.1.card

/-- Definition: For a collection s of subsets of V, we denote by closure s the smallest ASC over V containing all elements in s
as faces.

Remark: Here we secretly consider the ambient space as the simplex with vertex set V.
-/
abbrev closure (s : Set (Finset V))
  : AbstractSimplicialComplex V := sInf {K | s ⊆  K.faces}

lemma subset_closure_faces (s : Set (Finset V)) : s ⊆ (closure s).faces := by
  simp only [sInf_def, Set.coe_setOf, Set.mem_setOf_eq, Set.subset_iInter_iff, Subtype.forall,
    imp_self, forall_const]

lemma closure_mono {s t: Set (Finset V)} : s ⊆ t → closure s ≤ closure t := by
  intro hst
  apply sInf_le_sInf
  rw [Set.setOf_subset_setOf]
  intro _ h; exact Set.Subset.trans hst h

/--
Lemma: For a finset f, the closure of {f} is the simplex of f.
-/
lemma closure_simplex (f : Finset V) : closure {f} =  simplex f := by
  have h1 : (closure {f}).faces = (simplex f).faces:= by
    apply Set.Subset.antisymm
    · rw [sInf_def]
      rintro s h1
      simp only [Set.singleton_subset_iff, mem_faces, Set.mem_setOf_eq, Set.mem_iInter, Set.coe_setOf, Subtype.forall] at h1
      exact h1 (simplex ↑f) fun ⦃_⦄ a => a
    · rw [sInf_def]
      rintro s h1
      apply simplex_face.1 at h1
      simp only [Finset.coe_subset] at h1
      simp only [Set.singleton_subset_iff, mem_faces, Set.mem_setOf_eq, Set.mem_iInter, Set.coe_setOf, Subtype.forall]
      intro i fi
      apply mem_faces.1 <| i.lower' h1 <| mem_faces.2 fi
  exact instSetLikeAbstractSimplicialComplexFinset.proof_1 (closure {f}) (simplex ↑f) h1

def closureSingleton (f : Finset V) : AbstractSimplicialComplex V where
  faces :=
    if Nonempty f then
      {t | t.toSet ⊆ f}
    else
      {∅}
  empty_mem := by
    by_cases h : Nonempty f <;> simp [h]
  lower' := by
    by_cases h : Nonempty f <;> simp [h]
    · exact antitone_le
    · exact Finset.isLowerSet_singleton_empty V

/-- Explicit construction of `closure s` for `s : Set (Finset V)`-/
def closurePower (s : Set (Finset V)) : AbstractSimplicialComplex V where
  faces :=
    if Nonempty s then
      ⨆ f : s, {t | t.toSet ⊆ f}
    else
      {∅}
  empty_mem := by
    by_cases h : Nonempty s <;> simp [h]
    exact nonempty_subtype.mp h
  lower' := by
    by_cases h : Nonempty s <;> simp [h]
    · refine isLowerSet_iUnion₂ ?_
      intro t _
      intro a b h1 h2
      refine' Set.Subset.trans ?_ h2
      congr
    · exact Finset.isLowerSet_singleton_empty V

theorem closure_union_eq_iSup_closure {ι : Type*} (p : ι → Set (Finset V)) :
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
Lemma: Let s be a collection of finsets in V. Then the closure of s is just the union of the closure of elements in s.

Remark: So taking closure commuts with taking union.
-/
lemma closure_eq_iSup (s : Set (Finset V)) : closure s = ⨆ f : s,  closure {f.1} := by
  rw [← closure_union_eq_iSup_closure,
    Set.iUnion_singleton_eq_range, Subtype.range_coe_subtype, Set.setOf_mem_eq]

theorem closure_eq_closurePower (s: Set (Finset V)) : closure s = closurePower s := by
  sorry

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

/--
Definition: G is a cone over F with cone point x if
x ∈ G.vertices - F.vertices
s ∈ F ⇔ s ∪ {x} ∈ G.
-/
def Cone (F G: AbstractSimplicialComplex V) (x : V) :=
  x ∈ G.vertices \ F.vertices ∧
  ∀ s, s ∈ F.faces ↔ s ∪ {x} ∈ G.faces

def isCone (G: AbstractSimplicialComplex V) := ∃ F x, Cone F G x

lemma cons_pure (hc : Cone F G x) (hp : Pure F) : Pure G := by sorry

/- the following lemma is not true -/
-- lemma cons_pure' (hc : isCone G) : Pure G := by sorry

end AbstractSimplicialComplex

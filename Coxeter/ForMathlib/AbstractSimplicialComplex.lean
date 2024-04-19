import Mathlib.Order.UpperLower.Hom
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice

/--
An abstract simplicial complex is a pair (V,F) where V is a set and F is a set of finite subsets of V such that
  (1) ∅ ∈ F,
  (2) if s ∈ F and t ⊆ s, then t ∈ F.
-/
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
    have h3 : G.faces = F.faces := Set.Subset.antisymm h1 h2
    exact SetLike.ext' h3

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
  sInf := fun s => ⟨⋂ F ∈ s, F.faces,
    Set.mem_biInter (fun F _ => F.empty_mem) ,
    isLowerSet_iInter₂ (fun F _ => F.lower')⟩

@[simp]
lemma sInf_def (s : Set (AbstractSimplicialComplex V)) : (sInf s).faces = ⋂ F ∈ s, F.faces := by rfl

lemma sInf_isGLB (s : Set (AbstractSimplicialComplex V)) : IsGLB s (sInf s) := by
  constructor
  . intro F hF
    simp only [sInf, le_def, Set.biInter_subset_of_mem hF]
  . intro G hG
    simp_rw [mem_lowerBounds,le_def] at hG
    rw [le_def,sInf_def]
    simp only [Set.subset_iInter_iff]
    exact hG


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
  faces := ⋃ F ∈ s, F.faces
  empty_mem := by
    simp [Set.mem_iUnion]
    rcases hs with ⟨e, he⟩
    exact ⟨e, he, e.empty_mem⟩
  lower' := isLowerSet_iUnion fun i ↦ isLowerSet_iUnion fun _ ↦ i.lower'

lemma sSup_eq_unionSubset {s : Set <| AbstractSimplicialComplex V} (hs : s.Nonempty) : sSup s = unionSubset hs  := by
  apply le_antisymm
  · apply sSup_le
    intro b bs
    rw [le_def]
    refine Set.subset_iUnion_of_subset b ?_
    refine Set.subset_iUnion_of_subset bs ?_
    rfl
  · rw [le_sSup_iff]
    intro b hb
    rw [le_def]
    exact Set.iUnion_subset fun i ↦ Set.iUnion_subset fun hi ↦ hb hi

def OfEmpty : AbstractSimplicialComplex V where
  faces := {∅}
  empty_mem := rfl
  lower' := Finset.isLowerSet_singleton_empty V

lemma bot_eq_ofEmpty : (⊥ : AbstractSimplicialComplex V) = OfEmpty := by
  symm
  rw [eq_bot_iff, le_def, show OfEmpty.faces = {∅} by rfl, Set.singleton_subset_iff]
  apply (⊥ : AbstractSimplicialComplex V).empty_mem


theorem bot_faces_eq_empty : (⊥ : AbstractSimplicialComplex V).faces = {∅} := by
  rw [bot_eq_ofEmpty]; rfl

@[simp]
lemma sSup_faces_of_nonempty {s : Set (AbstractSimplicialComplex V)} (h : s.Nonempty) : (sSup s).faces = ⋃ F ∈ s, F.faces := by
  rw [sSup_eq_unionSubset h]; rfl

/--
Definition: For any ASC F, we denote by vertices F the set of vertices of F.
-/
def vertices (F : AbstractSimplicialComplex V) : Set V := ⋃ s ∈ F.faces, s.toSet

/--
Definition: Let F be an ASC. A maximal face of F is called a facet of F.
-/
def IsFacet (F : AbstractSimplicialComplex V) (s : Finset V) := s ∈ F ∧  ∀ t ∈ F, s ⊆ t → s = t

/--
Definition: For any ASC F, we denote by Facets F the set of facets of F.
-/
def Facets (F : AbstractSimplicialComplex V) : Set (Finset V) := { s | F.IsFacet s}

/-
theorem Facets_nonempty {F : AbstractSimplicialComplex V} : Nonempty F.Facets := by
  by_cases h : F.faces = {∅}
  · have : ∀ s ∈ F, ∅ = s := by
      intro s hs
      rw [←mem_faces,h] at hs
      rw [eq_comm]; exact Set.eq_of_mem_singleton hs
    have hemp: IsFacet F ∅ := by
      simp [IsFacet]
      exact ⟨F.empty_mem,this⟩
    have empsub : ∅ ∈ F.Facets := by
     simp [Facets]
     assumption
    exact Nonempty.intro ⟨∅,empsub⟩
    --确实有一个极大元s存在的证明
  · have aux : ∃ s, s ∈ F ∧  ∀ t ∈ F, s ⊆ t → s = t := by sorry
    --感觉是不太对 根据structure定义 faces : Set (Finset V) -- the set of faces
    --如果吃无限个Finset V，那face就变成了infinite set，怎么取到这个maximal element

    /-V : Type u_1
      F : AbstractSimplicialComplex V
      h : ¬F.faces = {∅}
      --这个其实看着比较奇怪，理论上这句话后应该有两种情况，
         F.faces这个集族真的是空集，貌似根据structure的定义可以排除
         F.faces是含有∅及其他元素的集族
      aux : ∃ s ∈ F, ∀ t ∈ F, s ⊆ t → s = t
⊢ Nonempty ↑(Facets F)-/

    rcases aux with ⟨s, hs, h⟩
    have h1: IsFacet F s := ⟨hs,h⟩
    exact Nonempty.intro ⟨s,h1⟩

    /- 比较弱智的证明，在这里无脑simp之后的根据等式操作只有在lean中才能出现，
       自然语言中显然不会有人想到这么细节的数理结构
    simp[IsFacet] at h1
    simp[Facets,IsFacet]
    exact⟨ s, h1⟩
    --尖括号是一个structure，可以看到

    s : Finset V
    hs : s ∈ F
    h : ∀ t ∈ F, s ⊆ t → s = t
    h1 : s ∈ F ∧ ∀ t ∈ F, s ⊆ t → s = t
    ⊢ ∃ s ∈ F, ∀ t ∈ F, s ⊆ t → s = t

    对于⟨ s, h1⟩相当于直接带入
         [s : Finset V ]  为goal中的 [∃ s ∈ F] ,
         [h1 : s ∈ F ∧ ∀ t ∈ F, s ⊆ t → s = t中的and符右边部分] 为goal中的  [∀ t ∈ F, s ⊆ t → s = t]
    因而证明完成
       -/

-/
/-- Definition: A pure abstract simplicial complex is an abstract simplicial complex
    where all facets have the same cardinality. -/
def IsPure (F : AbstractSimplicialComplex V) :=
  ∀ s∈ Facets F, ∀ t ∈ Facets F, s.card = t.card

class Pure (F : AbstractSimplicialComplex V) where
  pure : ∀ s ∈ F.Facets, ∀ t ∈  F.Facets, s.card = t.card

/--Definition: We will call an ASC pure of rank `d` if all its facets has `d` elements-/
def IsPure' (F : AbstractSimplicialComplex V) (d : ℕ):=
  --∀ s ∈ F.faces, s.card = d
  --这个我真心感觉错了，怎么可能Pure‘里面是Facets这里IsPure'变成了faces
  ∀ s ∈ F.Facets, s.card = d

class Pure' (F : AbstractSimplicialComplex V) (d :ℕ) where
  pure : ∀ s ∈ F.Facets, s.card = d

lemma isPure_iff_isPure' {F : AbstractSimplicialComplex V} : F.IsPure ↔ ∃ d, F.IsPure' d := by
  by_cases hemp : Nonempty F.Facets
  · constructor
    · let s := Classical.choice (hemp)
      intro hIp
      use s.1.card
      intro t ht
      exact hIp t ht s s.2
    · intro hIp'
      obtain ⟨d, hIp'⟩ := hIp'
      -- rcases hIp' with ⟨d, hIp'⟩ 在这里用rcases和obtain效果是完全一样的
      intro s hs t ht
      rw [hIp' s hs, hIp' t ht]
  · constructor
    · intro
      use 0
      simp only [IsPure', Finset.card_eq_zero]
      contrapose! hemp
      rcases hemp with ⟨d, ⟨a, b⟩⟩
      use d
    · intro h
      rcases h with ⟨d, a⟩
      simp only [nonempty_subtype, not_exists] at hemp
      intro s hs t _
      exfalso
      exact hemp s hs











lemma pure_def {F : AbstractSimplicialComplex V} [Pure F] : ∀ s ∈ F.Facets, ∀  t ∈ F.Facets,  s.card = t.card := Pure.pure

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
  : AbstractSimplicialComplex V := sInf { K | s ⊆  K.faces}

/--
Lemma: For a finset f, the closure of {f} is the simplex of f.
-/
lemma closure_simplex (f : Finset V) : closure {f} =  simplex f := by sorry

/--
Lemma: Let s be a collection of finsets in V. Then the closure of s is just the union of the closure of elements in s.

Remark: So taking closure commuts with taking union.
-/
lemma closure_eq_iSup (s : Set (Finset V)) : closure s =  ⨆ f ∈ s,  closure {f} := by sorry

/--
Lemma: Let F be an ASC. Then the closure of the set of faces is just F.
-/
lemma closure_self {F : AbstractSimplicialComplex V} : closure (F.faces) = F := by
  sorry


lemma closure_mono {s t: Set (Finset V)} : s ⊆ t → closure s ≤ closure t := by
  intro hst; repeat rw [closure]
  apply sInf_le_sInf
  rw [Set.setOf_subset_setOf]
  intro _ h; exact Set.Subset.trans hst h



lemma closure_le {F : AbstractSimplicialComplex V} (h: s ⊆ F.faces) : closure s ≤ F := by sorry


/--
Definition: G is a cone over F with cone point x if
x ∈ G.vertices - F.vertices
s ∈ F ⇔ s ∪ {x} ∈ G.
-/

def Cone (F G: AbstractSimplicialComplex V) (x : V) :=
  x ∈ G.vertices \ F.vertices ∧
  ∀ s, s ∈ F.faces ↔ s ∪ {x} ∈ G.faces

def isCone (G: AbstractSimplicialComplex V) := ∃ F x, Cone F G x

instance cons_pure {h : Cone F G x} : Pure G := by sorry

instance cons_pure' {h : isCone G} : Pure G := by sorry

end AbstractSimplicialComplex

import Mathlib.Order.UpperLower.Hom
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice

/-
An abstract simplicial complex is a pair (V,F) where V is a set and F is a set of finite subsets of V such that
  (1) ∅ ∈ F,
  (2) if s ∈ F and t ⊆ s, then t ∈ F.
-/
structure AbstractSimplicialComplex (V : Type*)  where
  faces : Set (Finset V) -- the set of faces
  empty_mem : ∅ ∈ faces
  lower' : IsLowerSet faces -- The set of faces is a lower set under the inclusion relation.

open Classical

namespace AbstractSimplicialComplex

variable {V : Type*}

lemma subset_mem (F : AbstractSimplicialComplex V) : ∀ {s t}, s ∈ F.faces →  t ⊆ s → t ∈ F.faces := fun hs hst => F.lower' hst hs

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

/-
The simplex with verteces s ⊆ V is the complex of all finite subsets of s.
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

instance complete_lattice : CompleteLattice (AbstractSimplicialComplex V)
where
  inf := fun F G => ⟨F.faces ∩ G.faces, Set.mem_inter F.empty_mem G.empty_mem, IsLowerSet.inter F.lower' G.lower'⟩
  le_inf := fun _ _ _ hab hac _ ha =>
    Set.mem_inter (hab ha) (hac ha)
  inf_le_right := fun _ _ _ ha =>
      ha.2
  inf_le_left := fun _ _ _ ha => ha.1
  __ := completeLatticeOfInf (AbstractSimplicialComplex V) sInf_isGLB


@[simp]
lemma sSup_faces (s : Set (AbstractSimplicialComplex V)) : (sSup s).faces = ⋃ F ∈ s, F.faces := by sorry

def vertices (F : AbstractSimplicialComplex V) : Set V := ⋃ s ∈ F.faces, s.toSet

def IsFacet (F : AbstractSimplicialComplex V) (s : Finset V) := s ∈ F ∧  ∀ t ∈ F, s ⊆ t → s = t

def Facets (F : AbstractSimplicialComplex V) : Set (Finset V) := { s | F.IsFacet s}

/- Definition: A pure abstract simplicial complex is an abstract simplicial complex where all facets have the same cardinality. -/
def IsPure (F : AbstractSimplicialComplex F) :=
  ∀ s∈ Facets F, ∀ t ∈ Facets F, s.card = t.card

class Pure (F : AbstractSimplicialComplex F) where
  pure : ∀ s ∈ F.Facets, ∀ t ∈  F.Facets, s.card = t.card

/-We will call an ASC pure of rank `d` if all its facets has `d` elements-/
def IsPure' (F : AbstractSimplicialComplex F) (d : ℕ):=
  ∀ s ∈ F.faces, s.card = d

class Pure' (F : AbstractSimplicialComplex F) (d :ℕ) where
  pure : ∀ s ∈ F.Facets, s.card = d

lemma isPure_iff_isPure' {F : AbstractSimplicialComplex F} : F.IsPure ↔ ∃ d, F.IsPure' d := by
  sorry


lemma pure_def {F : AbstractSimplicialComplex V} [Pure F] : ∀ s ∈ F.Facets, ∀  t ∈ F.Facets,  s.card = t.card := Pure.pure

lemma pure_isPure {F : AbstractSimplicialComplex V} [Pure F] : IsPure F := pure_def

/-
If the size of simplices in F is unbounded, it has rank 0 by definition.

Remark: We should general be careful with the unbounded case.
-/
noncomputable def rank (F : AbstractSimplicialComplex V) : ℕ := iSup fun s : F.faces => s.1.card

--def clousre (F: AbstractSimplic)

-- F is ASC, complete s is ASC.
-- F ∩ s = F ∩ (complete s)

abbrev closure (s : Set (Finset V))
  : AbstractSimplicialComplex V := sInf { K | s ⊆  K.faces}

-- For a finset f, the closure of {f} is the simplex of f.
lemma closure_simplex (f : Finset V) : closure {f} =  simplex f := by sorry

lemma closure_eq_iSup (s : Set (Finset V)) : closure s =  ⨆ f ∈ s,  closure {f} := by sorry

lemma closure_self {F : AbstractSimplicialComplex V} : closure (F.faces) = F := by
  sorry

lemma closure_mono {s t: Set (Finset V)} : s ⊆ t → closure s ≤ closure t := by
  intro hst; repeat rw [closure]
  apply sInf_le_sInf
  rw [Set.setOf_subset_setOf]
  intro _ h; exact Set.Subset.trans hst h

/-
??
-- -/
-- def closure' {F : AbstractSimplicialComplex V} (s : Set (F.faces))
--   : AbstractSimplicialComplex V := by sorry

-- lemma closure'_eq_closure {F : AbstractSimplicialComplex V} (s : Set (F.faces)) : closure' s = F ⊓ closure s := by sorry

-- def closure_face {F : AbstractSimplicialComplex V} (s : F.faces)
--   : AbstractSimplicialComplex V := by sorry

lemma closure_le {F : AbstractSimplicialComplex V} (h: s ⊆ F.faces) : closure s ≤ F := by sorry

/-
G is a cone over F with cone point x if
x ∈ G.vertices - F.vertices
s ∈ F ⇔ s ∪ {x} ∈ G.
-/
def Cone (F G: AbstractSimplicialComplex V) (x : V) :=
  x ∈ G.vertices \ F.vertices ∧
  ∀ s, s ∈ F.faces ↔ s ∪ {x} ∈ G.faces

def isCone (G: AbstractSimplicialComplex V) := ∃ F x, Cone F G x

end AbstractSimplicialComplex

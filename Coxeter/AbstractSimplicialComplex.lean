import Coxeter.CoxeterSystem
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Card
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Data.List.Lex
import Mathlib.Order.Cover
import Coxeter.Aux_

open Classical


/- Reference for posets :
      1. Combinatorics of Coxeter groups by Anders Bjorner and Franacesco Brenti, Appendix A2
-/

section ASC

/-
An abstract simplicial complex is a pair (V,F) where V is a set and F is a set of finite subsets of V such that
  (1) ∅ ∈ F,
  (2) if s ∈ F and t ⊆ s, then t ∈ F.
-/
structure AbstractSimplicialComplex (V : Type*)  where
  faces : Set (Finset V) -- the set of faces
  empty_mem : ∅ ∈ faces
  subset_mem : ∀ {s t}, s ∈ faces →  t ⊆ s → t ∈ faces

namespace AbstractSimplicialComplex

variable {V : Type*}

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



def facet (F : AbstractSimplicialComplex V) (s : Finset V) := s ∈ F ∧ ∀ t ∈ F.faces, s ⊆ t → s = t

def Facets (F : AbstractSimplicialComplex V) : Set (F.faces) := { s : F.faces | facet F s}

/-
Lemma: The set of facets is a subset of faces of the ASC F.
-/
lemma Facets_subset_faces {F : AbstractSimplicialComplex V} (s : Finset V) : s ∈ F.faces := sorry

/- Definition: A pure abstract simplicial complex is an abstract simplicial complex where all facets have the same cardinality. -/
def isPure (F : AbstractSimplicialComplex F) :=
  ∀ s t : Facets F,  s.1.1.card =t.1.1.card

class Pure (F : AbstractSimplicialComplex F) where
  pure : ∀ s t : Facets F, s.1.1.card = t.1.1.card

lemma pure_eq {F : AbstractSimplicialComplex V} [Pure F] {s t : Facets F} : s.1.1.card = t.1.1.card := by
  exact Pure.pure s t

lemma pure_isPure {F : AbstractSimplicialComplex V} [Pure F] : isPure F := by intro s t; exact pure_eq

/-
If the size of simplices in F is unbounded, it has rank 0 by definition.

Remark: We should general be careful with the unbounded case.
-/
noncomputable def rank (F : AbstractSimplicialComplex V) : ℕ := iSup fun s : F.faces => s.1.card


-- To be removed.
--  def intersect (F : AbstractSimplicialComplex V) (s : Set V) : AbstractSimplicialComplex V where
--   faces := {t | t ∈ F.faces ∧ t.toSet ⊆ s}
--   empty_mem := by
--     exact ⟨F.empty_mem, by simp only [Finset.coe_empty, Set.empty_subset]⟩
--   subset_mem := by
--     intro a b h1 h2
--     constructor
--     . exact F.subset_mem h1.1 h2
--     . refine' Set.Subset.trans ?_ h1.2
--       congr



/-
Definition: Let F and G be a ASCs over V. Then their intersection (of the sets of faces) is also an ASC.
-/
def Intersect_two (F : AbstractSimplicialComplex V) (G : AbstractSimplicialComplex V) : AbstractSimplicialComplex V where
  faces := {t | t ∈ F.faces ∧ t ∈ G.faces}
  empty_mem := by
    exact ⟨F.empty_mem, G.empty_mem⟩
  subset_mem := by
    intro s t h g
    let ⟨h1, h2⟩ := h
    constructor
    . apply F.subset_mem h1 g
    . apply G.subset_mem h2 g

def Intersect {m : ℕ} (s: Fin m → AbstractSimplicialComplex V) : AbstractSimplicialComplex V where
    faces := by sorry
    empty_mem := by sorry
    subset_mem := by sorry


/-
Instance: The set of all abstraci simplicial complexes with the anbiamt set V forms a complete lattices via intersection.
-/
instance lattice : CompleteLattice (AbstractSimplicialComplex V) := sorry


/-
Definition: Let s be a collection of finite subset of V.
Then we define the closure of s as the smallest simplicial complex containing all elements in s as faces.
-/
def closure {F : AbstractSimplicialComplex V} (s : Set (F.faces))
  : AbstractSimplicialComplex V := by sorry

def closure_face {F : AbstractSimplicialComplex V} (s : F.faces)
  : AbstractSimplicialComplex V := by sorry

lemma closure_singleton {F : AbstractSimplicialComplex V} (s : F.faces) : closure {s} = closure_face s := by sorry
/-
Lemma: Let s and t be collections of the finite subsets of V. Then if s ⊆ t, we have closure s ≤ closure t in the partial ordering.
-/
lemma closure_mono  {F : AbstractSimplicialComplex V} {s t: Set (F.faces)} : s ⊆ t → closure s ≤ closure t := by sorry


#check Subgroup.closure

/-
Definition: For any subset s of V, we denote by complete s as the simplicial complex with the vertex set s.
-/
/-
?? We can change complete to simplex. The Mathlib only has geometric simplicial complexes.
-/
def complete (s : Set V) : AbstractSimplicialComplex V where
  faces := {t | t.toSet ⊆ s}
  empty_mem := by simp
  subset_mem := by
    intro a b h1 h2
    refine' Set.Subset.trans ?_ h1
    congr

@[simp]
lemma complete_face' {s : Set V} {a : Finset V} : a ∈ (complete s).faces ↔ a.toSet ⊆ s := by
  simp only [complete, Set.mem_setOf_eq]

@[simp]
lemma complete_face {s : Set V} {a : Finset V} : a ∈ (complete s) ↔ a.toSet ⊆ s := by
  refine complete_face'

-- To be removed.
/-
-- Lemma: The closure of a facet is the complete complex of the facet, i.e., a simplicial complex.
-- -/
-- lemma closure_face_eq_complete {F : AbstractSimplicialComplex V} {s : Finset V} (h : s ∈ F) : intersect F s = complete s := by
--   apply SetLike.ext';ext a
--   constructor
--   . intro ha
--     exact complete_face.2 ha.2
--   . intro ha
--     have ha' : a ⊆ s := complete_face.1 ha
--     rw [intersect]
--     constructor
--     . exact subset_mem F h ha'
--     . congr


/-
Definition: Let F be a pure abstract simplicial complex of dim m.
A shelling of F is an linear ordering l_1, ⋯ , l_n of all (maximal) facets of F such that
 cl(l_i) ∩ (∪_{j < i} cl(l_j)) (=Hi) is an abstract simplicial complex pure of dimension m -1.

 Recall that intersections and unions of ASCs are still ACSs.
-/

def shelling (F : AbstractSimplicialComplex V)  [Pure F]  {m : ℕ} (l : Fin m ≃ Facets F) :=
  ∀ i : Fin m, let Gi : AbstractSimplicialComplex V := closure_face (l i);
  let si := Sup fun l : Fin m → Facets F;

  Gi = si i ⊔ si i


  let Hi := Intersect (s : fun j => closure_face (l j))
  let Hi := (closure_face ((l i) ∩ (Finset.biUnion (Finset.filter (. < i) (Finset.univ : Finset (Fin m))) (fun j => (l j)))))
  isPure Hi ∧ rank Hi + 1= rank F

/-
Definition': Let F be a pure abstract simplicial complex of dim m.
A shelling of F is an linear ordering l_1, ⋯ , l_n of all (maximal) facets of F such that
 for any j < i, there exists j' < i, such that l_i ∩ l_j ⊂ l_i ∩ l_{j'} and |l_i ∩ l_{j'}| = m-1.
-/
def shelling' (F :  AbstractSimplicialComplex V) [Pure F]  {m : ℕ } (l : Fin m ≃ Facets F) := ∀ i j : Fin m, j < i →
∃ k : Fin m, k < i ∧ ((l i).1.1 ∩ (l j) ⊂ (l i) ∩ (l k)) ∧ ((l i).1.1 ∩ (l k)).card = (l i).1.1.card - 1


/-
Lemma: The two definitions of shellings are equivalent.
-/
lemma equiv_shelling {V : Type*} (F : AbstractSimplicialComplex V) [Pure F]  {m : ℕ } (l : Fin m ≃ Facets F) :
    shelling F l ↔ shelling' F l := by sorry

/-
Definition: An abstract simplicial complex F is called shellable, if it admits a shelling.
-/
def shellable (F : AbstractSimplicialComplex V) [Pure F] := ∃ (m: ℕ) (l : Fin m ≃ Facets F), shelling' F l

end AbstractSimplicialComplex

section Coe

/- Suppose s t are a finset in V.
  Then the descent t' of t is the element in Finset s
  such that {x.val  : x ∈ t' } = t ∩ s.
-/
noncomputable def finset_descent {V : Type*} (s t : Finset V) : Finset s := Finset.filter (fun x:s => x.1 ∈ t) (Finset.univ :Finset s)

@[simp]
lemma finset_descent_eq {V : Type*} {s t : Finset V} : Finset.image (·.val) (finset_descent s t)  = t ∩ s := by
  rw [finset_descent]
  ext x
  constructor <;> simp

lemma finset_descent_eq_subset {V : Type*} {s t : Finset V} (h : t ⊆ s): Finset.image (·.val) (finset_descent s t)  = t := by
  rw [finset_descent_eq]
  exact Finset.inter_eq_left.2 h

def closure' {V : Type*} (F : Set (Finset V)) (F: AbstractSimplicialComplex V) (s : Finset V) :
  Set (Finset s) := (finset_descent s ·) '' closure F s


instance closure_ASC {V : Type*} (F : Set (Finset V)) [F: AbstractSimplicialComplex V] (s : Finset V)
  : @AbstractSimplicialComplex _ (closure F s) where
  empty_mem := sorry
  singleton_mem := sorry
  subset_mem := sorry

end Coe

end ASC

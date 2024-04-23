import Mathlib.Data.Set.Card
import Coxeter.ForMathlib.ASCShelling

namespace ASCShellingProps

open AbstractSimplicialComplex
open Classical

variable {V : Type*} --[DecidableEq V]

def Deletion (F : AbstractSimplicialComplex V) (x : V) : Set F.faces :=
  {f | x ∉ f.1}

def DeletionSimplex (F : AbstractSimplicialComplex V) (x : V) : AbstractSimplicialComplex V where
  faces := Deletion F x
  empty_mem := by
    simp only [Deletion, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, mem_faces,
      exists_and_left, exists_prop, exists_eq_right_right, Finset.not_mem_empty, not_false_eq_true,
      true_and]
    exact F.empty_mem
  lower' := by
    simp only [Deletion]
    intro _ _ hab ha
    simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, mem_faces, exists_and_left,
      exists_prop, exists_eq_right_right] at ha ⊢
    constructor
    · have := ha.1
      contrapose! this
      exact hab this
    · exact F.lower' hab ha.2

def Link (F : AbstractSimplicialComplex V) (x : vertices F) : Set F.faces :=
  {f | x.1 ∉ f.1 ∧ {x.1} ∪ f.1 ∈ F.faces}

def LinkSimplex (F : AbstractSimplicialComplex V) (x : vertices F) : AbstractSimplicialComplex V where
  faces := Link F x
  empty_mem := by
    simp only [Set.mem_image, Subtype.exists, mem_faces, exists_and_right, exists_eq_right, Link]
    use F.empty_mem
    simp only [Set.mem_setOf_eq, Finset.not_mem_empty, not_false_eq_true, Finset.union_empty,
      true_and]
    exact (vertices_iff_singleton_set_face F x).mpr x.2
  lower' := sorry

def LinkFace (F : AbstractSimplicialComplex V) (s : F.faces) : Set F.faces :=
  {f | s.1 ∩ f.1 = ∅ ∧ s.1 ∪ f.1 ∈ F.faces }

def Star (F : AbstractSimplicialComplex V) (s : F.faces) : Set F.faces :=
  {f | s.1 ∪ f.1 ∈ F.faces }

lemma LinkFace_subset_Star (F : AbstractSimplicialComplex V) (s : F.faces) :
  LinkFace F s ⊆ Star F s := fun _ h ↦ h.2

-- see if we can remove Fintype V
-- something is off, need to check empty set
def VertexDecomposable [Fintype V] (F : AbstractSimplicialComplex V) : Prop :=
  (Pure F) ∧ ((∃ (f : Finset V), F = simplex f) ∨
  (∃ (x : vertices F), (DeletionSimplex F x.1).rank = F.rank ∧ VertexDecomposable (DeletionSimplex F x) ∧
  (LinkSimplex F x).rank + 1 = F.rank ∧ VertexDecomposable (LinkSimplex F x)))
termination_by (F.rank, (vertices F).ncard)
decreasing_by
  all_goals simp_wf
  sorry
  sorry


-- Page 83: define VertexDecomposable, SheddingVertex
-- create new file to do property 1, import ASC shelling, merge to master before taking

end ASCShellingProps

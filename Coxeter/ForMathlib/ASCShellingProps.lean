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
  lower' t s st tF := by
    simp only [Link, mem_faces, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_left,
      exists_prop, exists_eq_right_right] at tF ⊢
    rcases tF with ⟨⟨x_t, xtF⟩, tF⟩
    refine ⟨?_, F.lower' st tF⟩
    refine ⟨fun a => x_t (st a), ?_⟩
    refine mem_faces.mp (F.lower' ?_ xtF)
    exact Finset.union_subset_union_right st

def LinkFace (F : AbstractSimplicialComplex V) (s : F.faces) : Set F.faces :=
  {f | s.1 ∩ f.1 = ∅ ∧ s.1 ∪ f.1 ∈ F.faces }

def Star (F : AbstractSimplicialComplex V) (s : F.faces) : Set F.faces :=
  {f | s.1 ∪ f.1 ∈ F.faces }

lemma LinkFace_subset_Star (F : AbstractSimplicialComplex V) (s : F.faces) :
  LinkFace F s ⊆ Star F s := fun _ h ↦ h.2

lemma delete_vertex (F : AbstractSimplicialComplex V) (x : vertices F) :
    vertices F \ {x.1} = (vertices (DeletionSimplex F x.1)) := by
  ext t
  simp [DeletionSimplex, Deletion]
  constructor
  · intro h
    simp [Set.image]
    use {t}
    simp only [id_eq, Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Finset.coe_eq_singleton,
      Subtype.exists, exists_prop, exists_eq_right, Finset.mem_singleton, Set.mem_singleton_iff,
      and_true]
    refine And.intro ?_ ((vertices_iff_singleton_set_face F t).mpr h.1)
    by_contra a
    rw [a] at h
    exact h.2 rfl
  · rintro ⟨s, ⟨⟨a, ha⟩, hts⟩⟩
    refine And.intro ⟨s, And.intro ?_ hts⟩ ?_
    · simp only [Set.image, Set.range, Set.mem_setOf_eq]
      have := a.2
      simp only [id_eq, Set.mem_image, Set.mem_setOf_eq, Subtype.exists, mem_faces, exists_and_left,
        exists_prop, exists_eq_right_right] at this
      refine ⟨⟨a.1, this.2⟩, ?_⟩
      rw [← ha]
    · by_contra tx
      rw [tx, ← ha] at hts
      --apply a.2.2.1
      sorry
      /-have : x.1 ∈ a.1 := by
        sorry
      sorry
      --simp [ha]-/

lemma terminating_size [Fintype V] (F : AbstractSimplicialComplex V) (x : vertices F) :
    (vertices (DeletionSimplex F x.1)).ncard < (vertices F).ncard := by
  sorry

-- Consider replacing Fintype V -> Fintype (vertices F)
def VertexDecomposableInductive (r n : ℕ) [Fintype V] (F : AbstractSimplicialComplex V)
    (h1 : r = F.rank) (h2 : n = (vertices F).ncard) : Prop :=
  match r, n with
  | 0, _ => True
  --| _, 0 => True
  | r' + 1, _ => (Pure F) ∧ (∃ (f : Finset V), F = simplex f) ∨
      (∃ (x : vertices F), (by
    let nd := (vertices (DeletionSimplex F x.1)).ncard
    let nl := (vertices (LinkSimplex F x)).ncard
    by_cases h : ((DeletionSimplex F x.1).rank = r' + 1) ∧ (LinkSimplex F x).rank = r'
    · have := terminating_size F x
      refine VertexDecomposableInductive (r' + 1) nd (DeletionSimplex F x) h.1.symm rfl ∧
        VertexDecomposableInductive r' nl (LinkSimplex F x) h.2.symm rfl
    · exact False
      ))

lemma fin_vertex_iff_fin_faces (F : AbstractSimplicialComplex V) : Finite F.faces ↔ Finite (vertices F) := by
  sorry

def VertexDecomposable [Fintype V] (F : AbstractSimplicialComplex V) : Prop :=
  VertexDecomposableInductive F.rank (vertices F).ncard F rfl rfl

-- see if we can remove Fintype V
-- something is off, need to check empty set



-- Page 83: define VertexDecomposable, SheddingVertex
-- create new file to do property 1, import ASC shelling, merge to master before taking

end ASCShellingProps

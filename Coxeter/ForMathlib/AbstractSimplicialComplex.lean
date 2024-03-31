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


def IsFacet (F : AbstractSimplicialComplex V) (s : Finset V) := s ∈ F ∧  ∀ t ∈ F, s ⊆ t → s = t

def Facets (F : AbstractSimplicialComplex V) : Set (Finset V) := { s | F.IsFacet s}

/- Definition: A pure abstract simplicial complex is an abstract simplicial complex where all facets have the same cardinality. -/
def IsPure (F : AbstractSimplicialComplex F) :=
  ∀ s t : Facets F, s.1.card = t.1.card

class Pure (F : AbstractSimplicialComplex F) where
  pure : ∀ s t : Facets F, s.1.card = t.1.card

lemma pure_eq {F : AbstractSimplicialComplex V} [Pure F] {s t : Facets F} : s.1.card = t.1.card := by
  exact Pure.pure s t

lemma pure_isPure {F : AbstractSimplicialComplex V} [Pure F] : IsPure F := by intro s t; exact pure_eq

/-
If the size of simplices in F is unbounded, it has rank 0 by definition.
-/
noncomputable def rank (F : AbstractSimplicialComplex V) : ℕ := iSup fun s : F.faces => s.1.card

--def clousre (F: AbstractSimplic)

-- F is ASC, complete s is ASC.
-- F ∩ s = F ∩ (complete s)

abbrev closure (s : Set (Finset V))
  : AbstractSimplicialComplex V := sInf { K | s ⊆  K.faces}

-- For a finset f, the closure of {f} is the simplex of f.
lemma closure_simplex (f : Finset V) : closure {f} =  simplex s := by sorry

lemma closure_eq_iSup (s : Set (Finset V)) : closure s =  ⨆ (f : s),  closure {f.1} := by sorry

lemma closure_self {F : AbstractSimplicialComplex V} : closure (F.faces) = F := by
  sorry

lemma closure_mono {s t: Set (Finset V)} : s ⊆ t → closure s ≤ closure t := by
  intro hst; repeat rw [closure]
  apply sInf_le_sInf
  rw [Set.setOf_subset_setOf]
  intro _ h; exact Set.Subset.trans hst h


/-
?? I think we should remove singleton_mem in the defintion. Or how to make s to be type?
-/

--instance coe_Facets : CoeOut (Facets F) (Finset V) :=
--  ⟨fun s => s.val⟩


/- Definition: Let F be a pure abstract simplicial complex of dim m.
A shelling of F is an linear ordering l_1, ⋯ , l_n of all (maximal) facets of F such that
 l_i ∩ (∪_{j < i} l_j) (=Hi) is an abstract simplicial complex pure of dimension m -1.
-/

def shelling (F : AbstractSimplicialComplex V)  [Pure F]  {m : ℕ } (l : Fin m ≃ Facets F) :=
  ∀ i : Fin m, let Hi := (closure F ((l i).1 ∩ (Finset.biUnion (Finset.filter (. < i) (Finset.univ : Finset (Fin m))) (fun j => (l j).1))))
  isPure Hi ∧ rank Hi = rank F - 1

/-
Definition': Let F be a pure abstract simplicial complex of dim m.
A shelling of F is an linear ordering l_1, ⋯ , l_n of all (maximal) facets of F such that
 for any j < i, there exists j' < i, such that l_i ∩ l_j ⊂ l_i ∩ l_{j'} and |l_i ∩ l_{j'}| = m-1.
-/
def shelling' (F :  AbstractSimplicialComplex F)
 [Pure F]  {m : ℕ } (l : Fin m ≃ Facets F) := ∀ i j : Fin m, j < i → ∃ k : Fin m, k < i ∧ ((l i).1 ∩ (l j).1 ⊂ (l i).1 ∩ (l k).1) ∧ ((l i).1 ∩ (l k).1).card = (l i).1.card - 1


/- Lemma: The two definitions of shellings are equivalent.
-/
lemma equiv_shelling {V : Type*} (F : AbstractSimplicialComplex F) [Pure F]  {m : ℕ } (l : Fin m ≃ Facets F) :
    shelling F l ↔ shelling' F l := by sorry

/- Definition: An abstract simplicial complex F is called shellable, if it admits a shelling.
-/
def shellable (F : AbstractSimplicialComplex F) [Pure F] := ∃ (m: ℕ) (l : Fin m ≃ Facets F), shelling F l

end AbstractSimplicialComplex

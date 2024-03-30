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

namespace List

/- Definition: The adjacent pairs of a list [a_1,a_2, ⋯, a_n] is defined to be
  [(a_1, a_2), (a_2, a_3), ⋯, (a_{n-1}, a_n)].
  If the list L has length less than 2, the new list will be an empty list by convention. -/
def adjPairs {α  : Type*} : List α  → List (α × α )
  | [] => []
  | _ :: []  => []
  | a :: b :: l =>  ((a, b) : α  × α) ::  (b :: l).adjPairs

/-
Lemma: Let a b ∈ α, then for any list L of α, the pair (a,b) is an adjacent pair of the list [a,b,L].
-/
lemma adjPairs_cons {a b :α} {L : List α} : (a,b) ∈ (a::b::L).adjPairs:= by
  simp [List.adjPairs]

/-Lemma: Let h a b ∈ α and tail be a list of α. If (a,b) is an adjacent pair of tail, then (a,b) is an adjacent pair of [h, tail].
-/
lemma adjPairs_tail {h a b : α} {tail : List α} : (a,b) ∈ tail.adjPairs → (a,b) ∈ (h::tail).adjPairs:= by
  match tail with
  | [] => simp [adjPairs]
  | h' :: l' =>
    simp [adjPairs]
    intro h1
    right; exact h1

/- Definition (programming):
The adjacent extened pairs of a List L is a List of adjacent pairs of L together with the claim that e ∈ adjPairs L -/
def adjEPairs {α : Type*} (L : List α) : List ({e : α × α  | e ∈ L.adjPairs}) := match L with
  | [] => []
  | _ :: [] => []
  | a :: b :: l =>  ⟨(a, b), List.adjPairs_cons⟩ :: (List.map (fun e => ⟨e.val, List.adjPairs_tail e.prop ⟩) <| List.adjEPairs (b :: l))

end List



/- Reference for posets :
      1. Combinatorics of Coxeter groups by Anders Bjorner and Franacesco Brenti, Appendix A2
-/

open PartialOrder

namespace PartialOrder
/- Let P be a finite poet. -/
variable {P : Type*} [PartialOrder P]

/- Definition: We say a poset P is bounded, if it has a unique minimal and a unique maximal element. -/
#print BoundedOrder


/- Recall that : We say a is covered by b if x < y and there is no element z such that x < z < y. -/
/- Notation: We denote the cover relation by x ⋖ y. Use "\les" to type the symbol -/

/- Defintion: We define the set of edges of P as the set of all pairs (a,b) such that a is covered by b.-/
def edges (P : Type*) [PartialOrder P] : Set (P × P) := {(a, b) | a ⋖ b }


/-
Definition: A chain in the poset P is a finite sequence x₀ < x₁ < ⋯ < x_n.
-/
abbrev chain (L : List P) : Prop := List.Chain' (· < ·) L

section maximal_chain
/-
Definition: A chain in the poset P is maximal if it is not a proper subset of any other chains.
In other words, all relations are cover relations with x_0 being a minimal element and x_n be a maximal element.
-/

abbrev maximal_chain (L: List P) : Prop := chain L ∧
  ∀ L' : List P, chain L' -> List.Sublist L L' -> L = L'

/-
We also define the notion of maximal_chain' in the sense that if for any chain L' whose head and tail are the same as that of L, then L is sublist of L' implies L = L'.
 -/
abbrev maximal_chain' (L: List P) : Prop := chain L ∧ ∀ L' : List P, chain L' → (L.head? = L'.head? ∧ L.getLast? = L'.getLast?) → List.Sublist L L' -> L = L'

lemma maximal_chain'_of_maximal_chain {L: List P} : maximal_chain L → maximal_chain' L := by
  intro h
  constructor
  . exact h.1
  . intro L' hL' _ h2
    exact h.2 L' hL' h2

lemma chain_singleton {a : P} : chain [a] := by
  constructor

lemma chain_singleton_of_head_eq_tail  {L : List P} (a : P) : chain L → L.head? = some a → L.getLast? = some a → L.length = 1  := by
  sorry

lemma maximal_chain'_singleton {a : P}: maximal_chain' [a] := by
  sorry

lemma maximal_chain'_nil : maximal_chain' ([] : List P) := by
  constructor
  . simp
  . intro L' hL' h1 h2
    have : L'.head? = none := by simp [<-h1.1]
    cases L'
    . simp
    . simp at this


lemma maximal_chain'_head {a b: P} {tail : List P} : maximal_chain' (a :: b :: tail) → a ⋖ b := by
  apply Function.mtr
  intro h H
  have hab : a < b := (List.chain'_cons.1 H.1).1
  obtain ⟨c, hc1⟩ := (not_covBy_iff hab).1 h
  let L' := a :: c :: b :: tail
  have chainL' : chain L' := by
    rw [ (by simp : L' = [a,c] ++ b:: tail)]
    apply (List.chain'_split (a := b) (l₂ := tail)).2
    constructor
    . simp [hc1]
    . exact (List.chain'_cons.1 H.1).2
  have hL' : List.Sublist (a :: b :: tail) L' := by
    apply  List.cons_sublist_cons.2
    apply  List.sublist_cons
  have neqL' : a :: b :: tail ≠ L' := by
    intro h
    rw [List.cons_eq_cons,List.cons_eq_cons] at h
    exact List.cons_ne_self _ _ (Eq.symm h.2.2)
  exact H.2 L' chainL' ⟨rfl, rfl⟩ hL' |> neqL'


lemma maximal_chain'_tail {a : P} {tail : List P} : maximal_chain' (a :: tail) → maximal_chain' tail := by
  rintro ⟨C, MAX⟩
  cases tail with
  | nil => exact maximal_chain'_nil
  | cons b t =>
  constructor
  . exact List.Chain'.tail C
  . intros L' hL' h1 h2
    let tail := b ::t
    let L'' := a :: L'
    have chainL'' : chain L'' := by
      apply List.chain'_cons'.2
      constructor
      . intro t ht
        rw [<-h1.1] at ht
        have : b=t := by simp [List.head?_cons] at ht; exact ht
        rw [<-this]
        exact (List.chain'_cons.1 C).1
      . exact hL'
    have htL''1 : (a :: tail).head? = L''.head?  := by simp
    have htL''2 : (a :: tail).getLast? = L''.getLast? := by
      cases L' with
      | nil => simp at h2
      | cons c d =>
        simp only [List.getLast?_cons_cons, h1.2]
    have sublistL'' : List.Sublist (a :: tail) L'' := by
      apply List.cons_sublist_cons.2
      exact h2
    have : a :: tail = L'' := MAX L'' chainL'' ⟨htL''1, htL''2⟩ sublistL''
    exact (List.cons_eq_cons.1 this).2

lemma maximal_chain'_cons {a b : P} {L : List P} : maximal_chain' (b :: L) → a ⋖ b → maximal_chain' (a :: b :: L) := by sorry

/-
a pair of element is a maximal chain if and only if the pair is a cover relation.
-/
lemma maximal_chain'₂_iff_ledot {a b : P} : maximal_chain' [a,b] ↔ (a ⋖ b) := by sorry

/-
Lemma: If a chain L : x₀ < x₁ < ⋯ < x_n is maximal', then we have x_0 ⋖ x_1 ⋖ x_2 ⋯ ⋖ x_n.
-/
lemma maximal_chain'_cover {P : Type*} [PartialOrder P] {L: List P} :
  maximal_chain' L → List.Chain' (· ⋖ ·) L := by
  intro h
  induction' L with a t ih
  . simp
  . match t with
    | [] => simp
    | b :: t' =>
      apply List.chain'_cons.2
      exact ⟨maximal_chain'_head h, ih (maximal_chain'_tail h)⟩

/-
Lemma: If a chain L : x₀ < x₁ < ⋯ < x_n is maximal, then we have x_0 ⋖ x_1 ⋖ x_2 ⋯ ⋖ x_n.
-/
lemma maximal_chain_cover {P : Type*} [PartialOrder P] {L: List P} :
  maximal_chain L → List.Chain' (· ⋖ · ) L := fun h =>
  maximal_chain'_cover <| maximal_chain'_of_maximal_chain h


/-
Lemma: Assume P is a bounded poset. Let L : x₀ < x₁ < ⋯ < x_n  be a chain of P
such that the adjacent relations are cover relations; x_0 is the minimal element and x_n is the maximal element.
Then L is a maximal chain.
-/
lemma maximal_chain'_of_cover_chain {P :Type*} [PartialOrder P]  {L: List P} :
  List.Chain' (· ⋖ ·) L → maximal_chain' L := by sorry
/-
Lemma: Assume P is a bounded poset. Let L : x₀ < x₁ < ⋯ < x_n  be a chain of P
such that the adjacent relations are cover relations; x_0 is the minimal element and x_n is the maximal element.
Then L is a maximal chain.
-/
lemma maximal_chain_of_ledot_chain {P :Type*} [PartialOrder P] [BoundedOrder P] {L: List P} :
  List.Chain' (· ⋖ · ) L ∧ L.head? = some ⊥ ∧ L.getLast? = some ⊤ → maximal_chain L := by
  rintro ⟨h1, h2, h3⟩
  by_contra h4
  rw [maximal_chain] at h4
  push_neg at h4
  sorry


/-
Lemma: Let P be a bounded finite poset. Then a maximal chain exsits.
-/
lemma exist_maximal_chain {P : Type*} [PartialOrder P] [BoundedOrder P] [Fintype P] :
  ∃ L : List P, maximal_chain L := by sorry


/-
(Programming) Note that the assumption that P is a BoundedOrder implies that P is nonempty, and so a maximal chain is nonempty.
-/
lemma max_chain_nonempty {P : Type*} [PartialOrder P] [BoundedOrder P]  [Fintype P] (L: List P) :
  maximal_chain L → L ≠ [] := by
  intro h1
  by_contra h2
  rw [h2] at h1
  simp only [maximal_chain] at h1
  have h3 : List.Sublist [] (⊥ :: []) := by
    apply List.nil_sublist ((⊥ : P) :: [])
  have h4 : chain (⊥ :: []) := by
    exact List.chain'_singleton (⊥ : P)
  have h5 : [] = (⊥ :: []) := by
    apply h1.2
    · exact h4
    · exact h3
  have h6 : 0 = 1 := by
    rw [←List.length_nil, h5, List.length_singleton]
  linarith

/-
Lemma: Let P be a bounded finite poset. Let L = [x_0, ⋯, x_m] be a list of elements in P.
Then L is a maximal chain if and only if  x_0 is the minimal element, x_n is the maximal element, and x_i ⋖ x_{i+1} for all i.
-/
lemma ledot_max_chain {P : Type*} [PartialOrder P] [BoundedOrder P]  [Fintype P] (L: List P) :
  maximal_chain L ↔ ((L.head? = (⊥ : P)) ∧ (L.getLast? = (⊤ : P)) ∧ (List.Chain' ledot L)) := by sorry

/-
Lemma: Let L : x_0 < x_1 < ⋯ < x_n be a maximal chain of P. Then (x_i, x_{i+1}) is an (cover) edge of P.
-/
lemma max_chain_mem_edge {P : Type*} [PartialOrder P] {L: List P} {e: P × P} :
  maximal_chain L →  e ∈ L.adjPairs → e ∈ edges P:= sorry


/-
We define the set of all maximal chains of P.
-/
abbrev maximalChains (P : Type*) [PartialOrder P] : Set (List P) := { L | maximal_chain L }

/-
(Programming)
-/

def edgePairs {P : Type*} [PartialOrder P] (L : maximalChains P) : List (edges P) :=
  List.map (fun e => ⟨e.val, max_chain_mem_edge L.prop  e.prop⟩) <| L.val.adjEPairs

/-
?? this is often called rank.
-/
/- Define corank to be the maximal lenght of a maximal chain
  Note that if the length is unbounded,then corank =0.
 -/
noncomputable def corank (P : Type*) [PartialOrder P] : ℕ := iSup fun L : maximalChains P => L.val.length


end maximal_chain




@[deprecated Set.Icc]
def Interval {P : Type*} [PartialOrder P] (x y : P) : Set P := {z | x ≤ z ∧ z ≤ y}

instance Interval.bounded {P : Type*} [PartialOrder P] {x y : P} (h : x ≤ y) : BoundedOrder (Set.Icc x y) where
  top := ⟨y, And.intro h (le_refl y)⟩
  bot := ⟨x, And.intro (le_refl x) h⟩
  le_top := fun x ↦ x.2.2
  bot_le := fun x ↦ x.2.1

instance Interval.poset {P : Type*} [PartialOrder P] {x y : P} :
PartialOrder (Set.Icc x y) := by exact Subtype.partialOrder _

instance Interval.edge_coe {P : Type*} [PartialOrder P] {x y : P} : CoeOut (edges (Set.Icc x y)) (edges P) where
  coe := fun z => ⟨(z.1.1, z.1.2),sorry ⟩



end PartialOrder


section GradedPoset

/-
Definition: A finite poset P is called graded if it is pure and bounded.
A poset is called pure if all maximal chains are of the same length.
-/
class GradedPoset (P : Type*) [PartialOrder P][Fintype P] extends BoundedOrder P where
  pure: ∀ (L₁ L₂ : List P), ((maximal_chain L₁) ∧ (maximal_chain L₂)) → (L₁.length = L₂.length)

/-
Definition/Lemma : The corank of a graded poset is the length of any maximal chain in P.
-/
lemma GradedPoset.corank {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P]: ∀ L : maximalChains P, corank P = L.val.length := by sorry
/-
?? this is often called rank.
-/
end GradedPoset


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



def facet (F : AbstractSimplicialComplex V) (s : Finset V) := s ∈ F ∧  ∀ t ∈ F, s ⊆ t → s = t

def Facets (F : AbstractSimplicialComplex V) : Set (Finset V) := { s | facet F s}

/- Definition: A pure abstract simplicial complex is an abstract simplicial complex where all facets have the same cardinality. -/
def isPure (F : AbstractSimplicialComplex F) :=
  ∀ s t : Facets F, s.1.card = t.1.card

class Pure (F : AbstractSimplicialComplex F) where
  pure : ∀ s t : Facets F, s.1.card = t.1.card

lemma pure_eq {F : AbstractSimplicialComplex V} [Pure F] {s t : Facets F} : s.1.card = t.1.card := by
  exact Pure.pure s t

lemma pure_isPure {F : AbstractSimplicialComplex V} [Pure F] : isPure F := by intro s t; exact pure_eq

/-
If the size of simplices in F is unbounded, it has rank 0 by definition.
-/
noncomputable def rank (F : AbstractSimplicialComplex V) : ℕ := iSup fun s : F.faces => s.1.card


def intersect (F : AbstractSimplicialComplex V) (s : Set V) : AbstractSimplicialComplex V where
  faces := {t | t ∈ F.faces ∧ t.toSet ⊆ s}
  empty_mem := by
    exact ⟨F.empty_mem, by simp only [Finset.coe_empty, Set.empty_subset]⟩
  subset_mem := by
    intro a b h1 h2
    constructor
    . exact F.subset_mem h1.1 h2
    . refine' Set.Subset.trans ?_ h1.2
      congr

--def clousre (F: AbstractSimplic)

-- F is ASC, complete s is ASC.
-- F ∩ s = F ∩ (complete s)

instance lattice : CompleteLattice (AbstractSimplicialComplex V) := sorry

def closure (s : Set (Finset V))
  : AbstractSimplicialComplex V := sInf { K | s ⊂ K.faces}

lemma closure_self {F : AbstractSimplicialComplex V} : closure (F.faces) = F := by sorry

lemma closure_mono {s t: Set (Finset V)} : s ⊆ t → closure s ≤ closure t := by sorry


#check Subgroup.closure
/-
The complete complex of a subset s of V is the complex of all finite subsets of s.
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

/-
The closure of a facet is the complete complex of the facet.
-/
lemma closure_face_eq_complete {F : AbstractSimplicialComplex V} {s : Finset V} (h : s ∈ F) : (closure F s) = complete s := by
  apply SetLike.ext';ext a
  constructor
  . intro ha
    exact complete_face.2 ha.2
  . intro ha
    have ha' : a ⊆ s := complete_face.1 ha
    rw [closure]
    constructor
    . exact subset_mem F h ha'
    . congr


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

def closure' {V : Type*} (F : Set (Finset V)) [AbstractSimplicialComplex F] (s : Finset V) :
  Set (Finset s) := (finset_descent s ·) '' closure F s


instance closure_ASC {V : Type*} (F : Set (Finset V)) [AbstractSimplicialComplex F] (s : Finset V)
  : @AbstractSimplicialComplex _ (closure F s) where
  empty_mem := sorry
  singleton_mem := sorry
  subset_mem := sorry

end Coe

end ASC


/-
Reference : 1. On lexicographically shellable poset by Ander Bjornder and Michelle Wachs, Transaction AMS.
-/



section Shellable

variable {P : Type*} [PartialOrder P] --[Fintype P] [GradedPoset P]

/-
Definition: Let P be a poset. Let Delta(P) be the set of all chains in P.
Note that each element in Delta(P) will considered as a chain.
-/
@[simp]
def Delta_List (P : Type*) [PartialOrder P] : Set (List P) := {L : List P | chain L}


/-
Definition: Let P be a poset. Let Delta.ASC (P) be the set of all chains in P.
Note that each element in Delta.ASC (P) will considered as a subset of P.
-/

@[simp]
def Delta (P : Type*) [PartialOrder P] : Set (Finset P) := List.toFinset '' Delta_List P

/- Definition: Let P be a poset. We define a partial order on Delta_List(P) by containment.
-/
instance Delta_List.partialOrder {P : Type*} [PartialOrder P] : PartialOrder (Delta_List P) where
  le := fun x y =>  List.Sublist x.1 y.1
  le_refl := fun x => List.Sublist.refl x.1
  le_trans := sorry
  le_antisymm := sorry
  lt_iff_le_not_le := sorry

/-
Definition: Let P be a poset. Then Delta (P) is an abstract simplicial complex.
-/

instance Delta_List.AbstractSimplicialComplex {P : Type*} [PartialOrder P] : AbstractSimplicialComplex (Delta P) where
  empty_mem := by simp only [Delta, Delta_List, Set.mem_image, Set.mem_setOf_eq,
    List.toFinset_eq_empty_iff, exists_eq_right,chain,List.Chain']
  singleton_mem := by
    intro v; simp only [Delta, Set.mem_image]
    use [v]
    constructor
    . simp only [Delta_List, Set.mem_setOf_eq,chain,List.chain'_singleton]
    . trivial
  subset_mem := by
    intro s h1 t h2
    simp only [Delta, Set.mem_image] at h1 h2
    rcases h1 with ⟨L, h1, h1'⟩
    dsimp
    use (List.filter (fun (x : P) => x ∈ t) L)
    sorry

/-
Definition: Let P be a graded poset. Then Delta.ASC (P) is a pure abstract simplicial complex.
-/
instance Delta.Pure {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P]: AbstractSimplicialComplex.Pure (Delta P) where
  pure := sorry

/-
Definition: Let P be a graded poset. We say P is shellable, if the order complex Delta.ASC is shellable.
-/
def Shellable (P : Type*) [PartialOrder P] [Fintype P] [GradedPoset P] :=
  AbstractSimplicialComplex.shellable (Delta P)

-- /-
-- ??? The following is incorrect. But one might want to add some preliminary lemma for shellable posets.
-- -/
-- noncomputable def shelling_aux {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P] (l : List <| maximalChains P) : Prop := match l with
--   | [] => true
--   | _ :: [] => true
--   | a :: b :: l' => (a.1.toFinset ∩ (List.foldl (fun (x : Finset P) (y : maximalChains P)
--                 => x ∪ y.1.toFinset ) Finset.empty (b :: l'))).card == a.1.length - 1

-- /- Note that the shelling condition implies that l has no duplicates-/
-- def shelling' {P :Type*} [PartialOrder P] [Fintype P] [GradedPoset P] (l : List <| maximalChains P) :=
--   (∀ x : maximalChains P, x ∈ l)
--     ∧ List.Forall shelling_aux l.tails

-- def Shellable' (P : Type*) [PartialOrder P] [Fintype P] [GradedPoset P] := ∃ l : List (maximalChains P),  shelling' l



end Shellable



section labeling
namespace PartialOrder
variable {P : Type*} [PartialOrder P] --[Fintype P] [GradedPoset P]
variable {A : Type*} [PartialOrder A]

/-
Definition: Let P and A be posets. An edge labelling of P in A is a map from the set of edges of P to the poset A.
-/
@[simp]
abbrev edgeLabeling (P A : Type*) [PartialOrder P] := edges P  → A

/-
Definition: Let P and A be posets and l be an edge labelling of P in A.
Then any maximal chain m : x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n in P, we define a list in A by [l(x_0 ⋖ x_1),l(x_1 ⋖ x_2), ⋯ ,l(x_{n-1} ⋖ x_n)].
-/
def mapMaxChain (l : edgeLabeling P A) (m : maximalChains P)  : List A := List.map (fun e => l e) <| edgePairs m

/-
Definition: Let P and A be posets and l be an edge labelling of P in A.
Then any maximal chain m : x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n in [x,y] ⊂ P, we define a list in A by [l(x_0 ⋖ x_1),l(x_1 ⋖ x_2), ⋯ ,l(x_{n-1} ⋖ x_n)].
-/
def mapMaxChain_interval (l : edgeLabeling P A) {x y : P} (m : maximalChains <| Set.Icc x y)  : List A := List.map (fun e : edges (Set.Icc x y) => l (e : edges P)) <| edgePairs m

/-Defines the set of risingChians in an interval [x,y]-/
abbrev risingChains (l : edgeLabeling P A) (x y: P) := {m : maximalChains <| Set.Icc x y | List.Chain' (. ≤ .) <| mapMaxChain_interval l m}

/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
class EL_labeling (l : edgeLabeling P A) where
  unique {x y: P} (h : x<y) : Unique (risingChains l x y)
  unique_min {x y: P} (h : x<y): ∀ (m' : maximalChains <| Set.Icc x y), m' ≠ (unique h).default → (mapMaxChain_interval l (unique h).default.val < mapMaxChain_interval l m')

/-Theorem: Let P be a graded finite poset with an EL-labelling l to a poset A. Then P is shellable.
-/
theorem EL_shellable {P : Type*} [PartialOrder P] [PartialOrder A] [Fintype P] [GradedPoset P] (l : edgeLabeling P A) (h: EL_labeling l): Shellable P :=sorry


end PartialOrder
end labeling

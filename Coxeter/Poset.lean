import Coxeter.CoxeterSystem
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Card
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Data.List.Lex

open Classical

namespace List

/- The adjacent pairs of a list [a_1,a_2, ⋯, a_n] is defined to be
  [(a_1, a_2), (a_2, a_3), ⋯, (a_{n-1}, a_n)].
  If the list L has length less than 2, the new list will be an empty list by convention. -/
def adjPairs {α  : Type*} : List α  → List (α × α )
  | [] => []
  | _ :: []  => []
  | a :: b :: l =>  ((a, b) : α  × α) ::  (b :: l).adjPairs

lemma adjPairs_cons {a b :α} {L : List α} : (a,b) ∈ (a::b::L).adjPairs:= by
  simp [List.adjPairs]

lemma adjPairs_tail {h a b : α} {tail : List α} : (a,b) ∈ tail.adjPairs → (a,b) ∈ (h::tail).adjPairs:= by
  match tail with
  | [] => simp [adjPairs]
  | h' :: l' =>
    simp [adjPairs]
    intro h1
    right; exact h1

/- The adjacent extened pairs of is a List of adjacent pairs together with the claim that e ∈ adjPairs L -/
def adjEPairs {α : Type*} (L : List α) : List ({e : α × α  | e ∈ L.adjPairs}) := match L with
  | [] => []
  | _ :: [] => []
  | a :: b :: l =>  ⟨(a, b), List.adjPairs_cons⟩ :: (List.map (fun e => ⟨e.val, List.adjPairs_tail e.prop ⟩) <| List.adjEPairs (b :: l))

end List


-- Add references and comments
/- Reference : 1. Combinatorics of Coxeter groups by Anders Bjorner and Franacesco Brenti, Appendix A2
               2. On lexicographically shellable poset by Ander Bjornder and Michelle Wachs, Transaction AMS.
-/

open PartialOrder

namespace PartialOrder
/- Let P be a finite poet. -/
variable {P : Type*} [PartialOrder P]

/- Definition: We say a poset P is bounded, if it has a unique minimal and a unique maximal element. -/
#print BoundedOrder


/- Definition: We say a is covered by b if x < y and there is no element z such that x < z < y. -/
-- def ledot {P : Type*} [PartialOrder P] : P → P → Prop := sorry -- (a : P) → (b : P) → (a < b ∧ (∀ {c : P}, (a ≤ c ∧ c ≤ b) → (a = c ∨ b = c)))
def ledot {P : Type*} [PartialOrder P]  (a b : P) : Prop := (∀ c : P, (a ≤ c ∧ c ≤ b) → (a = c ∨ b = c))

/- Notation: We denote the cover relation by x ⋖ y. Use "\les" to type the symbol -/
notation a " ⋖ " b => ledot a b

/- Defintion: We define the set of edges of P as set of all pairs (a,b) such that a is covered by b.-/
def edges (P : Type*) [PartialOrder P] : Set (P × P) := {(a, b) | ledot a b }


/- Definition: We define an edge labelling of P as a function from the set of relations to another poset A.-/
/- Remark: We are interested in two cases :
  a is coverd by b;
  or a < b with at = b for some reflection t.
-/


/-
Definition: A chain in the poset P is a finite sequence x₀ < x₁ < ⋯ < x_n.
-/
def chain {P : Type*} [PartialOrder P] (L : List P) : Prop := List.Chain' (. < .) L

--#print List.Chain'


section maximal_chain
/-
Definition: A chain in the poset P is maximal if it is not a proper subset of any other chains.
In other words, all relations are cover relations with x_0 being a minimal element and x_n be a maximal element.
-/

def maximal_chain {P : Type*} [PartialOrder P] (L: List P) : Prop := chain L ∧
  ∀ L' : List P, chain L' -> List.Sublist L L' -> L = L'


/-
Lemma: If a chain L : x₀ < x₁ < ⋯ < x_n is maximal, then we have x_0 ⋖ x_1 ⋖ x_2 ⋯ ⋖ x_n.
-/
lemma maximal_chain_ledot {P : Type*} [PartialOrder P] {L: List P} :
  maximal_chain L → List.Chain' ledot L := sorry

lemma maximal_chain_of_ledot_chain {P :Type*} [PartialOrder P] [BoundedOrder P] {L: List P} :
  List.Chain' ledot L ∧ L.head? = some ⊥ ∧ L.getLast? = some ⊤ → maximal_chain L := sorry

/-
Lemma: Let P be a bounded finite poset. Then a maximal chain exsits.
-/
lemma exist_maximal_chain {P : Type*} [PartialOrder P] [BoundedOrder P] [Fintype P] :
  ∃ L : List P, maximal_chain L := by sorry


/-
Note that the assumption that P is a BoundedOrder implies that P is nonempty, and so a maximal chain is nonempty.
-/
lemma max_chain_nonempty {P : Type*} [PartialOrder P] [BoundedOrder P]  [Fintype P] (L: List P) :
  maximal_chain L → L≠ [] := by sorry

/-
Lemma: Let P be a bounded finite poset. Then a maximal chain exsits.
-/
lemma ledot_max_chain {P : Type*} [PartialOrder P] [BoundedOrder P]  [Fintype P] (L: List P) :
  maximal_chain L ↔ ((L.head? = (⊥ : P)) ∧ (L.getLast? = (⊤ : P)) ∧ (List.Chain' ledot L)) := by sorry

lemma max_chain_mem_edge {P : Type*} [PartialOrder P] {L: List P} {e: P × P} :
  maximal_chain L →  e ∈ L.adjPairs → e ∈ edges P:= sorry


/-
We define the set of all maximal chains of P.
-/
abbrev maximalChains (P : Type*) [PartialOrder P] : Set (List P) := { L | maximal_chain L }

--def adjPairs {P:Type*} [PartialOrder P] (L : maximalChains P) :
-- List (edges P) :=  L.val.adjPairs

/- Extended Chains is a pair (m,e) with e ∈ m -/
--def eChains (P : Type*) := { Le : List P × (P×P)| Le.2 ∈ List.adjPairs Le.1}


def edgePairs {P : Type*} [PartialOrder P] (L : maximalChains P) : List (edges P) :=
  List.map (fun e => ⟨e.val, max_chain_mem_edge L.prop  e.prop⟩) <| L.val.adjEPairs

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

/- Question: The difference between instance and theorem for the above.-/



end PartialOrder


section GradedPoset

/- Definition: A poset P is called graded if it is pure and bounded.
A poset is called pure if all maximal chains are of the same length.
-/
class GradedPoset (P : Type*) [PartialOrder P][Fintype P] extends BoundedOrder P where
  pure: ∀ (L₁ L₂ : List P), ((maximal_chain L₁) ∧ (maximal_chain L₂)) → (L₁.length = L₂.length)


lemma GradedPoset.corank {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P]: ∀ L : maximalChains P, corank P = L.val.length := by sorry

end GradedPoset

section labeling
namespace PartialOrder
variable {P : Type*} [PartialOrder P] --[Fintype P] [GradedPoset P]
variable {A : Type*} [PartialOrder A]


@[simp]
abbrev edgeLabeling (P A : Type*) [PartialOrder P] := edges P  → A

def mapMaxChain (l : edgeLabeling P A) (m : maximalChains P)  : List A := List.map (fun e => l e) <| edgePairs m


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

end PartialOrder
end labeling


section ASC

/-
An abstract simplicial complex is a pair (V,F) where V is a set and F is a set of finite subsets of V such that
  (1) ∅ ∈ F,
  (2) {v} ∈ F for all v ∈ V, (This is to ensure that ∪ F = V.)
  (3) if s ∈ F and t ⊆ s, then t ∈ F.
-/
class AbstractSimplicialComplex {V : Type*} (F : Set (Finset V))where
  empty_mem : ∅ ∈ F
  singleton_mem : ∀ v : V, {v} ∈ F
  subset_mem : ∀ s ∈ F, ∀ t ⊆ s, t ∈ F

namespace AbstractSimplicialComplex

variable {V : Type*} (F : Set (Finset V)) [AbstractSimplicialComplex F]

def maximal_facet {V : Type*} (F : Set (Finset V)) [AbstractSimplicialComplex F] (s : Finset V) := s ∈ F ∧  ∀ t ∈ F, s ⊆ t → s = t

def maximalFacets : Set (Finset V) := { s | AbstractSimplicialComplex.maximal_facet F s}

--instance coe_maximalFacets : CoeOut (maximalFacets F) (Finset V) :=
--  ⟨fun s => s.val⟩

noncomputable def rank : ℕ := iSup fun s : F => s.1.card


/- Definition: A pure abstract simplicial complex is an abstract simplicial complex where all maximal facets have the same cardinality. -/
class Pure (F : Set (Finset V)) [AbstractSimplicialComplex F] where
  pure : ∀ s t : maximalFacets F, s.1.card = t.1.card

def shelling {V : Type*} (F : Set (Finset V)) [AbstractSimplicialComplex F] [Pure F]  {m : ℕ } (l : Fin m ≃ maximalFacets F) :=
  ∀ i : Fin m, ((l i).1 ∩ (Finset.biUnion (Finset.filter (. < i) (Finset.univ : Finset (Fin m))) (fun j => (l j).1))).card = (l i).1.card -1

def shellable {V : Type*} (F : Set (Finset V)) [AbstractSimplicialComplex F] [Pure F] := ∃ (m: ℕ) (l : Fin m ≃ maximalFacets F), shelling F l

end AbstractSimplicialComplex

end ASC

section Shellable

variable {P : Type*} [PartialOrder P] --[Fintype P] [GradedPoset P]

@[simp]
def Delta (P : Type*) [PartialOrder P] : Set (List P) := {L : List P | chain L}

@[simp]
def Delta.ASC (P : Type*) [PartialOrder P] : Set (Finset P) := List.toFinset '' Delta P


instance Delta.partialOrder {P : Type*} [PartialOrder P] : PartialOrder (Delta P) where
  le := fun x y =>  List.Sublist x.1 y.1
  le_refl := fun x => List.Sublist.refl x.1
  le_trans := sorry
  le_antisymm := sorry
  lt_iff_le_not_le := sorry

instance Delta.AbstractSimplicialComplex {P : Type*} [PartialOrder P] : AbstractSimplicialComplex (Delta.ASC P) where
  empty_mem := by simp only [ASC, Delta, Set.mem_image, Set.mem_setOf_eq,
    List.toFinset_eq_empty_iff, exists_eq_right,chain,List.Chain']
  singleton_mem := by
    intro v; simp only [ASC, Set.mem_image]
    use [v]
    constructor
    . simp only [Delta, Set.mem_setOf_eq,chain,List.chain'_singleton]
    . trivial
  subset_mem := by
    intro s h1 t h2
    simp only [ASC, Set.mem_image] at h1 h2
    rcases h1 with ⟨L, h1, h1'⟩
    dsimp
    use (List.filter (fun (x : P) => x ∈ t) L)
    sorry

instance Delta.ASC.Pure {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P]: AbstractSimplicialComplex.Pure (Delta.ASC P) where
  pure := sorry

def Shellable (P : Type*) [PartialOrder P] [Fintype P] [GradedPoset P] :=
  AbstractSimplicialComplex.shellable (Delta.ASC P)



end Shellable

/-
Definition: A graded poset P is called shellable if there is an ordering L_1, ⋯ , L_m of all maximal
chains of P such that |L_i ∩ (∪_{j < i} L_{j})| = |L_i|- 1.
-/
/-
def Shellable (P : Type*) [PartialOrder P] [Fintype P] extends GradedPoset P where
  L: Fin m ≃ maximalChains P,
  (∀ i : Fin m, ((L i).val.toFinset ∩ (⋃  j : Fin i.val, (L ⟨j.val,by sorry⟩).val.toFinset)).card = (L i).toFinset.length -1)
-/



/-
class EL_labelling (P A : Type*) [PartialOrder P] [Finite P] [PartialOrder A] where
  edges : Set (P × P) := {(a, b) : P × P | ledot a b }
  EL : edges → A
  chainL : (x y : P) → (h : x ≤ y) → List (Interval x y h)
  max : (x y : P) → (h : x ≤ y) → @maximal_chain _ (Interval.poset h) (chainL x y h)
  chainL_edges : List.Chain' ledot (chainL x y h)
  Inc : chain ((List_pair (chainL x y h)).map EL)
  Unique : ∀ L1 : List (Interval x y h), (maximal_chain L1)→ chain ((List_pair L1).map EL)→ L1 = chainL x y h
  L_min : ∀ L1 : List (Interval x y h), (maximal_chain L1)  → ((List_pair (chainL x y h)).map EL) ≤ ((List_pair L1).map EL)

#check EL_labelling.chainL





--- begin experiment
section Experiement
variable (P : Type*) [PartialOrder P] (x y z: P) (h : x ≤ y)

def Interval.poset1 {P : Type*} [PartialOrder P] {x y : P} :
PartialOrder ({z | x ≤ z ∧ z ≤ y}) := by exact Subtype.partialOrder _

/- Question: can we just define the poset directly? Then the question is if we can pick out the carrier set.
-/

-- instance Interval.poset1 {P : Type*} [PartialOrder P] {x y : P} (h : x ≤ y) :
-- PartialOrder (Interval x y h) := by exact Subtype.partialOrder _

#check Interval x y h
example (a: z ∈ Interval x y h) : z ≤ y := by
  rw [Interval] at a
  rcases a with ⟨_, h2⟩
  exact h2

example : PartialOrder (Interval x y h) := by sorry

example (Q : Type*) [LE Q] [BoundedOrder Q] : PartialOrder Q := by apply?

class PartialBoundedOrder (P : Type*) extends PartialOrder P, BoundedOrder P


example : ∀ z ∈ Interval x y h, z ≤ y := by
  intro z h1
  rw [Interval] at h1
  exact h1.2


end Experiement
------ end experiment








/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
class EL_labelling (P A : Type*) [PartialOrder P] [Finite P][GradedPoset P] [PartialOrder A] where
  edges : Set (P × P) := {(a, b) : P × P | ledot a b }
  EL : edges → A
  chainL : (x y : P) → (h : x ≤ y) → List (Interval x y h)
  max : (x y : P) → (h : x ≤ y) → @maximal_chain _ (Interval.poset h) (chainL x y h)
  chainL_edges : List.Chain' ledot (chainL x y h)
  Inc : chain ((List_pair (chainL x y h)).map EL)
  Unique : ∀ L1 : List (Interval x y h), (maximal_chain L1)→ chain ((List_pair L1).map EL)→ L1 = chainL x y h
  L_min : ∀ L1 : List (Interval x y h), (maximal_chain L1)  → ((List_pair (chainL x y h)).map EL) ≤ ((List_pair L1).map EL)

#check EL_labelling.chainL

/-
Definition: A graded poset P is called shellable if there is an ordering L_1, ⋯ , L_m of all maximal
chains of P such that |L_i ∩ (∪_{j < i} L_{j})| = |L_i|- 1.
-/
def shellable (P : Type*) [PartialOrder P][Finite P] [GradedPoset P]: Prop := sorry
 --∃ (m:ℕ) (L: Fin m ≃ maximalChains P),
  --(∀ i : Fin m, ((L i).val.toFinset ∩ (⋃  j : Fin i.val, (L ⟨j.val,by sorry⟩).val.toFinset)).card = (L i).toFinset.length -1)




/- Get elements out of the list L-/

def pick_i {P : Type*} [PartialOrder P] (L : List P) (i : (Fin (L.length-1))) : P×P :=
   ((L.get ⟨i.1,by linarith [i.2]⟩),L.get ⟨i.1+1, by (linarith [i.2])⟩)


def EL_maximal_chain (P A : Type*) [PartialOrder P] [PartialOrder A][Finite P] [GradedPoset P] (L: List P) (h: maximal_chain L)
  (el : EL P A):= ∀ i, el ⟨((L.get ⟨i, by sorry⟩ ),(L.get ⟨i+1, by sorry⟩)),by sorry⟩ → (Fin n→ A)

/-
Definition: Let λ be an edge labelling of P and let x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n be a maximal chain. The
chain is called increasing if λ(x_0 ⋖ x_1) ≤ λ(x_1 ⋖ x_2) ≤ ⋯ ≤ λ(x_{n-1}} ⋖ x_n).
-/

def Increasing_chain  (P A : Type*) [PartialOrder P] [PartialOrder A] (L: List P) (h: maximal_chain L) : Prop
  := List.chain' ledot L

#print List.chain'_iff_get

/- Needs to define lexicographically ordering. -/



/- Theorem: Let P be a graded poset. If P admits an CL-labelling, then P is shellable. -/

theorem CL_shellable {P : Type*} [PartialOrder P] (h: CL_labelling P): shellable P:= by sorry


/- Theorem: Let P be a graded poset. If P admits an EL-labelling, then P admits an CL-labeling. -/
lemma EL_CL {P : Type*} [PartialOrder P] (h: EL_labelling P) : CL_labelling P := by sorry

/- Theorem: Let P be a graded poset. If P admits an EL-labelling, then P is shellable. -/

theorem EL_shellable {P : Type*} [PartialOrder P] [BoundedOrder P] (EL_labelling P A) : shellable P := by sorry

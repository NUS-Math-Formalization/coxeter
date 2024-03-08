import Coxeter.CoxeterSystem

import Mathlib.Data.Set.Card

open Classical
namespace Shelling

-- Add references and comments
/- Reference : 1. Combinatorics of Coxeter groups by Anders Bjorner and Franacesco Brenti, Appendix A2
               2. On lexicographically shellable poset by Ander Bjornder and Michelle Wachs, Transaction AMS.
-/

/- Let P be a finite poet. -/
variable {P : Type*} [PartialOrder P]

#print BoundedOrder

/- Definition: We say a poset P is bounded, if it has a unique minimal and a unique maximal element. -/
variable [BoundedOrder P]

/- Notations for mininal and maximal. -/

#check (⊥ : P)
#check (⊤ : P)

/- Definition: We say a is covered by b if x < y and there is no element z such that x < z < y. -/
def ledot (a b : P) := a < b ∧ (∀ {c : P}, (a ≤ c ∧ c ≤ b) → (a = c ∨ b = c))

/- Notation: We denote the cover relation by x ⋖ y -/
notation a " ⋖ " b => ledot a b

/- Defintion: We define the set of edges of P as set of all pairs (a,b) such that a is covered by b.-/
def edges (P : Type*) [PartialOrder P] : Set (P × P) := {(a, b) | ledot a b }



/- Definition: We define an edge labelling of P as a function from the set of cover relations to another poset A.-/
def EL (P A : Type*) [PartialOrder P] := edges P → A

/-
Definition: A chain in the poset P is a finite sequence x₀ < x₁ < ⋯ < x_n.
-/
def chain {P : Type*} [PartialOrder P] (L: List P) : Prop := List.Chain' (. < .) L

#print List.Chain'

/- Definitio: The length of a chain is defined to be the cardinality of the underlying set -1. -/


/-
Definition: A chain in the poset P is maximal if it is not a proper subset of any other chains.
In other words, all relations are cover relations with x_0 being a minimal element and x_n be a maximal element.
-/

def maximal_chain {P : Type*} [PartialOrder P] (L: List P) : Prop := chain L ∧
  ∀ L' : List P, chain L' -> List.Sublist L L' -> L = L'

lemma maximal_chain_ledot {P : Type*} [PartialOrder P] (L: List P) (h: chain L) (h1 : maximal_chain L): Prop := sorry
  -- ∀ i :
  -- ((L.head h = (⊥ : P)) ∧ (L.getLast h = (⊤ : P)) ∧ (List.Chain' ledot L)) := by sorry

lemma exist_maximal_chain {P : Type*} [PartialOrder P] [BoundedOrder P] [Finite P] :
  ∃ L : List P, maximal_chain L := by sorry

lemma ledot_max_chain {P : Type*} [PartialOrder P] [BoundedOrder P]  [Finite P] (L: List P) (h : L ≠ []) :
  maximal_chain L ↔ ((L.head h = (⊥ : P)) ∧ (L.getLast h = (⊤ : P)) ∧ (List.Chain' ledot L)) := by sorry

/-
We define the set of all maximal chains of P.
-/
def maximalChains (P : Type*) [PartialOrder P] : Set (List P) := { L | maximal_chain L }

/- Definition: If all maximal chains are of the same length, then P is called pure. -/


/- Definition: A poset P is called graded if it is pure and bounded.-/
class GradedPoset (P : Type*) [PartialOrder P] extends BoundedOrder P where
  pure: ∀ (L₁ L₂ : List P), ((maximal_chain L₁) ∧ (maximal_chain L₂)) → (L₁.length = L₂.length)

/-
Definition: A graded poset P is called shellable if there is an ordering L_1, ⋯ , L_m of all maximal
chains of P such that |L_i ∩ (∪_{j < i} L_{j})| = |L_i|- 1.
-/
def shellable (P : Type*) [PartialOrder P] [GradedPoset P]: Prop := sorry
 --∃ (m:ℕ) (L: Fin m ≃ maximalChains P),
  --(∀ i : Fin m, ((L i).val.toFinset ∩ (⋃  j : Fin i.val, (L ⟨j.val,by sorry⟩).val.toFinset)).card = (L i).toFinset.length -1)


-- def CL_labelling (P : Type*) [PartialOrder P] (h: graded P): Prop := sorry

/-

How to hide the graded assmption.

-/

/- Get elements out of the list L-/

def pick_i {P : Type*} [PartialOrder P] (L : List P) (i : (Fin (L.length-1))) : P×P :=
   ((L.get ⟨i.1,by linarith [i.2]⟩),L.get ⟨i.1+1, by (linarith [i.2])⟩)


def EL_maximal_chain (P A : Type*) [PartialOrder P] [PartialOrder A] [GradedPoset P] (L: List P) (h: maximal_chain L)
  (el : EL P A):= ∀ i, el ⟨((L.get ⟨i, by sorry⟩ ),(L.get ⟨i+1, by sorry⟩)),by sorry⟩ → (Fin n→ A)

/-
Definition: Let λ be an edge labelling of P and let x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n be a maximal chain. The
chain is called increasing if λ(x_0 ⋖ x_1) ≤ λ(x_1 ⋖ x_2) ≤ ⋯ ≤ λ(x_{n-1}} ⋖ x_n).
-/

def Increasing_chain  (P A : Type*) [PartialOrder P] [PartialOrder A] (L: List P) (h: maximal_chain L) : Prop
  := List.chain' L

#print List.chain'_iff_get

/- Needs to define lexicographically ordering. -/

/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
def EL_labelling (P : Type*) [PartialOrder P] : Prop := sorry


/- Theorem: Let P be a graded poset. If P admits an CL-labelling, then P is shellable. -/

theorem CL_shellable {P : Type*} [PartialOrder P] (h: CL_labelling P): shellable P:= by sorry


/- Theorem: Let P be a graded poset. If P admits an EL-labelling, then P admits an CL-labeling. -/
lemma EL_CL {P : Type*} [PartialOrder P] (h: EL_labelling P) : CL_labelling P := by sorry

/- Theorem: Let P be a graded poset. If P admits an EL-labelling, then P is shellable. -/

theorem EL_shellable {P : Type*} [PartialOrder P] (h: EL_labelling P) : shellable P := by
  apply EL_CL at h
  apply CL_shellable h

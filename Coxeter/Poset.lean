import Coxeter.CoxeterSystem

import Mathlib.Data.Set.Card

namespace Shelling

-- Add references and comments
/- Reference : 1. Combinatorics of Coxeter groups by Anders Bjorner and Franacesco Brenti, Appendix A2
               2. On lexicographically shellable poset by Ander Bjornder and Michelle Wachs, Transaction AMS.
-/

/- Let P be a finite poet. -/
variable {P : Type*} [PartialOrder P] [Finite P]

/- Definition: We say a poset P is bounded, if it has a unique minimal and a unique maximal element. -/
def bounded (P : Type*) [PartialOrder P] : Prop := ∃ (x y : P), ∀ z : P, (x ≤ z ∧ z ≤ y)

/- Notations for mininal and maximal. -/

/- Definition: We say a is covered by b if x < y and there is no element z such that x < z < y. -/
def ledot (a b : P) := a < b ∧ (∀ {c : P}, (a ≤ c ∧ c ≤ b) → (a = c ∨ b = c))

/- Defintion: We define the set of edges of P as set of all pairs (a,b) such that a is covered by b.-/
def edges (P : Type*) [PartialOrder P] : Set (P × P) := {(a, b) | ledot a b }

/- Notation: We denote the cover relation by x ⋖ y -/

/- Definition: We define an edge labelling of P as a function from the set of cover relations to another poset A.-/
def EL (P A : Type*) [PartialOrder P] [PartialOrder A] := edges P → A

/-
Definition: A chain in the poset P is a finite sequence x₀ < x₁ < ⋯ < x_n.
-/
def chain {P : Type*} [PartialOrder P] (L: List P) : Prop := sorry

/- Definitio: The length of a chain is defined to be the cardinality of the underlying set -1. -/
def length {P : Type*} [PartialOrder P] (L: List P) (h: chain L): Prop := sorry


/-
Definition: A chain in the poset P is maximal if it is not a proper subset of any other chains.
In other words, all relations are cover relations with x_0 being a minimal element and x_n be a maximal element.
-/

def maximal_chain {P : Type*} [PartialOrder P] (L: List P): Prop := sorry

/-
We define the set of all maximal chains of P.
-/
def set_maximal_chains {P : Type*} [PartialOrder P] : Set (List P) := { L | maximal_chain L }

/- Definition: If all maximal chains are of the same length, then P is called pure. -/
def pure (P : Type*) [PartialOrder P] : Prop := ∀ (L₁ L₂ : List P), ((maximal_chain L₁) ∧ (maximal_chain L₂)) → (L₁.length = L₂.length)

/- Definition: A poset P is called graded if it is pure and bounded.-/
def graded (P : Type*) [PartialOrder P] : Prop := pure P ∧ bounded P

/-
Definition: A graded poset P is called shellable if there is an ordering L_1, ⋯ , L_m of all maximal
chains of P such that |L_i ∩ (∪_{j < i} L_{j})| = |L_i|- 1.
-/
def shellable (P : Type*) [PartialOrder P] (h: graded P): Prop := sorry

def CL_labelling (P : Type*) [PartialOrder P] (h: graded P): Prop := sorry

/-

How to hide the graded assmption.

-/
/-
Definition: Let λ be an edge labelling of P and let x_0 ⋖ x_1 ⋖ ⋯ ⋖ x_n be a maximal chain. The
chain is called increasing if λ(x_0 ⋖ x_1) ≤ λ(x_1 ⋖ x_2) ≤ ⋯ ≤ λ(x_{n-1}} ⋖ x_n).
-/

def Increasing_chain  (P : Type*) [PartialOrder P] (L: List P) (h: chain L) : Prop := sorry


/- Needs to define lexicographically ordering. -/

/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
def EL_labelling (P : Type*) [PartialOrder P] : Prop := sorry


/- Theorem: Let P be a graded poset. If P admits an CL-labelling, then P is shellable. -/

theorem CL_shellable {P : Type*} [PartialOrder P] (h: CL_labelling P) : shellable P := by sorry


/- Theorem: Let P be a graded poset. If P admits an EL-labelling, then P admits an CL-labeling. -/
lemma EL_CL {P : Type*} [PartialOrder P] (h: EL_labelling P) : CL_labelling P := by sorry

/- Theorem: Let P be a graded poset. If P admits an EL-labelling, then P is shellable. -/

theorem EL_shellable {P : Type*} [PartialOrder P] (h: EL_labelling P) : shellable P := by
  apply EL_CL at h
  apply CL_shellable h

import Coxeter.CoxeterSystem
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Card
import Mathlib.Init.Data.Ordering.Basic

open Classical
namespace Shelling

-- Add references and comments
/- Reference : 1. Combinatorics of Coxeter groups by Anders Bjorner and Franacesco Brenti, Appendix A2
               2. On lexicographically shellable poset by Ander Bjornder and Michelle Wachs, Transaction AMS.
-/

/- Let P be a finite poet. -/
variable {P : Type*} [PartialOrder P]

/- Definition: We say a poset P is bounded, if it has a unique minimal and a unique maximal element. -/
#print BoundedOrder


/- Definition: We say a is covered by b if x < y and there is no element z such that x < z < y. -/
def ledot {P : Type*} [PartialOrder P] : P → P → Prop := sorry -- (a : P) → (b : P) → (a < b ∧ (∀ {c : P}, (a ≤ c ∧ c ≤ b) → (a = c ∨ b = c)))
def led := (a : P) → (b : P) → (a ≤ b)

/-Bookmark:
ledot should be of type P → P → Prop
-/

/- Notation: We denote the cover relation by x ⋖ y -/
notation a " ⋖ " b => ledot a b

/- Defintion: We define the set of edges of P as set of all pairs (a,b) such that a is covered by b.-/
def Set_edges (P : Type*) [PartialOrder P] : Set (P × P) := {(a, b) | ledot a b }


/- Definition: For any list L = (x0, x1, ⋯ , x_n) in P, we define a new list in P × P by
((x0, x1), (x1,x2), ⋯ (x_{n-1}, x_n).
  If the list L has length less than 2, the new list will be an empty list by conventin. -/
def List_pair {P : Type*} [PartialOrder P] : List P → List (P × P)
  | [] => []
  | _ :: []  => []
  | a :: b :: l =>  ((a, b) : P × P) :: (List_pair (b :: l))

/- Definition: We define an edge labelling of P as a function from the set of relations to another poset A.-/
/- Remark: We are interested in two cases :
  a is coverd by b;
  or a < b with at = b for some reflection t.
-/



/-
Definition: A chain in the poset P is a finite sequence x₀ < x₁ < ⋯ < x_n.
-/
def chain {P : Type*} [PartialOrder P] (L : List P) : Prop := List.Chain' (. < .) L

#print List.Chain'


/-
Definition: A chain in the poset P is maximal if it is not a proper subset of any other chains.
In other words, all relations are cover relations with x_0 being a minimal element and x_n be a maximal element.
-/

def maximal_chain {P : Type*} [PartialOrder P] (L: List P) : Prop := chain L ∧
  ∀ L' : List P, chain L' -> List.Sublist L L' -> L = L'

lemma maximal_chain_ledot {P : Type*} [PartialOrder P] (L: List P) (h : maximal_chain L): Prop := sorry
  -- ∀ i :
  -- ((L.head h = (⊥ : P)) ∧ (L.getLast h = (⊤ : P)) ∧ (List.Chain' ledot L)) := by sorry
lemma maximal_chain_edges {P : Type*} [PartialOrder P] (L: List P) (h : maximal_chain L):
  Chain' ledot L := by sorry


lemma exist_maximal_chain {P : Type*} [PartialOrder P] [BoundedOrder P] [Finite P] :
  ∃ L : List P, maximal_chain L := by sorry

lemma ledot_max_chain {P : Type*} [PartialOrder P] [BoundedOrder P]  [Finite P] (L: List P) (h : L ≠ []) :
  maximal_chain L ↔ ((L.head h = (⊥ : P)) ∧ (L.getLast h = (⊤ : P)) ∧ (List.Chain' ledot L)) := by sorry


/-
We define the set of all maximal chains of P.
-/
def maximalChains (P : Type*) [PartialOrder P] : Set (List P) := { L | maximal_chain L }


/- Definition: A poset P is called graded if it is pure and bounded.-/
class GradedPoset (P : Type*) [PartialOrder P] extends BoundedOrder P where
  pure: ∀ (L₁ L₂ : List P), ((maximal_chain L₁) ∧ (maximal_chain L₂)) → (L₁.length = L₂.length)

def Interval {P : Type*} [PartialOrder P] (x y : P) (h : x ≤ y) : Set P := {z | x ≤ z ∧ z ≤ y}

-- def Interval.poset1 {P : Type*} [PartialOrder P] (x y : P) (h : x ≤ y) : Prop := sorry

instance Interval.bounded {P : Type*} [PartialOrder P] {x y : P} (h : x ≤ y) : BoundedOrder (Interval x y h) where
  top := ⟨y, And.intro h (le_refl y)⟩
  bot := ⟨x, And.intro (le_refl x) h⟩
  le_top := fun x ↦ x.2.2
  bot_le := fun x ↦ x.2.1

instance Interval.poset {P : Type*} [PartialOrder P] {x y : P} (h : x ≤ y) :
PartialOrder (Interval x y h) := by exact Subtype.partialOrder _

/- Question: The difference between instance and theorem for the above.-/




--- begin experiment
section
variable (P : Type*) [PartialOrder P] (x y z: P) (h : x ≤ y)

def Interval.poset1 {P : Type*} [PartialOrder P] {x y : P} (h : x ≤ y) :
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


end
------ end experiment








/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
class EL_labelling (P A : Type*) [PartialOrder P] [BoundedOrder P] [PartialOrder A] where
  edges : Set (P × P) := {(a, b) : P × P | ledot a b }
  EL : edges → A
  chainL : (x y : P) → (h : x ≤ y) → List (Interval x y h)
  max : (x y : P) → (h : x ≤ y) → @maximal_chain _ (Interval.poset h) (chainL x y h)
  chainL_edges : Prop := sorry
  -- chainPair : (x y : P) → (h : x ≤ y) → ((List_pair (chainL x y h)))
  Inc : (x y : P) → (h : x ≤ y) → @maximal_chain _ (Interval.poset h) (chainL x y h) ∧ chain ((List_pair (chainL x y h)).map EL)
  Unique : ∀ L1 L2 : List (Interval x y h), ((maximal_chain L1) ∧ (maximal_chain L2))→ (chain ((List_pair L1).map EL) ∧ chain ((List_pair L2).map EL)) → L1 = L2
  L_min : ∀ L1 L2 : List (Interval x y h), ((maximal_chain L1) ∧ (maximal_chain L2))



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
  := List.chain' ledot L

#print List.chain'_iff_get

/- Needs to define lexicographically ordering. -/



/- Theorem: Let P be a graded poset. If P admits an CL-labelling, then P is shellable. -/

theorem CL_shellable {P : Type*} [PartialOrder P] (h: CL_labelling P): shellable P:= by sorry


/- Theorem: Let P be a graded poset. If P admits an EL-labelling, then P admits an CL-labeling. -/
lemma EL_CL {P : Type*} [PartialOrder P] (h: EL_labelling P) : CL_labelling P := by sorry

/- Theorem: Let P be a graded poset. If P admits an EL-labelling, then P is shellable. -/

theorem EL_shellable {P : Type*} [PartialOrder P] (h: EL_labelling P) : shellable P := by
  apply EL_CL at h
  apply CL_shellable h

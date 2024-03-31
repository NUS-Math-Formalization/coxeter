import Coxeter.CoxeterSystem
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Card
import Mathlib.Init.Data.Ordering.Basic
import Mathlib.Data.List.Lex
import Mathlib.Order.Cover
import Coxeter.Aux_
import Coxeter.ForMathlib.AdjacentPair

open Classical


/- Reference for posets :
      1. Combinatorics of Coxeter groups by Anders Bjorner and Franacesco Brenti, Appendix A2
-/


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

import Coxeter.ForMathlib.PosetChain
import Coxeter.ForMathlib.PosetGraded
import Coxeter.ForMathlib.PosetShelling

namespace PartialOrder
variable {P : Type*} [PartialOrder P] [Fintype P]
variable {A : Type*} [PartialOrder A]

instance {x y : P} : Fintype (Set.Icc x y) := sorry -- temperory

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
def mapMaxChain_interval (l : edgeLabeling P A) {x y : P} (m : maximalChains <| Set.Icc x y)  : List A := List.map (fun e : edges (Set.Icc x y) => l ( sorry
    -- e : edges P
    )) <| edgePairs m

/-Defines the set of risingChians in an interval [x,y]-/
abbrev risingChains (l : edgeLabeling P A) (x y: P) := {m : maximalChains <| Set.Icc x y | List.Chain' (. ≤ .) <| mapMaxChain_interval l m}

/-
Definition: An edge labelling of P is called an EL-labelling if for every interval [x,y] in P,
  (1) there is a unique increasing maximal chain c in [x,y],
  (2) c <_L c' for all other maximal chains c' in [x,y].
Here <_L denotes the lexicographic ordering for the tuples in the labelling poset A.
-/
class ELLabeling (l : edgeLabeling P A) where
  unique {x y: P} (h : x<y) : Unique (risingChains l x y)
  unique_min {x y: P} (h : x<y): ∀ (m' : maximalChains <| Set.Icc x y), m' ≠ (unique h).default → (mapMaxChain_interval l (unique h).default.val < mapMaxChain_interval l m')

/-Theorem: Let P be a graded finite poset with an EL-labelling l to a poset A. Then P is shellable.
-/
theorem shellable_of_ELLabeling {P : Type*} [PartialOrder P] [PartialOrder A] [Fintype P] [GradedPoset P] (l : edgeLabeling P A) (h: ELLabeling l): Shellable P :=sorry


end PartialOrder

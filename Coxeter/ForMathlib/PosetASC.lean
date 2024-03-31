import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Coxeter.ForMathlib.AbstractSimplicialComplex
import Coxeter.ForMathlib.PosetChain

open Classical

section poset

namespace PartialOrder

variable {P : Type*} [PartialOrder P] --[Fintype P] [GradedPoset P]

/-
Definition: Let P be a poset. Let Delta(P) be the set of all chains in P.
Note that each element in Delta(P) will considered as a chain.
-/
@[simp]
def Delta_List (P : Type*) [PartialOrder P] : Set (List P) := {L : List P | chain L}


/-
Definition: Let P be a poset. Delta P is the set of all chains in P, which is an abstract simplicial complex.
Note that each element in Delta (P) will considered as a subset of P.
-/
@[simp]
abbrev Delta (P : Type*) [PartialOrder P] : AbstractSimplicialComplex P where
  faces := List.toFinset '' Delta_List P
  empty_mem := by simp
  lower' := by
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


end poset

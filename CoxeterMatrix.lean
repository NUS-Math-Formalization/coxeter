import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic

#eval Lean.versionString

variable {α: Type _}  {β: Type _}

@[ext,class] structure CoxeterMatrix:= 
(m : Matrix α α ℕ)
(isSymm : ∀ (a b : α ), m a b = m b a )
(one_iff: ∀  {a b : α}, (m a b = 1) ↔ (a=b) )

#check CoxeterMatrix
namespace CoxeterMatrix 

variable (m : @CoxeterMatrix α)

lemma Diag_is_one {s : α} : m.m s s = 1 := by
   rw [m.one_iff]

local notation  "F" => FreeGroup α

@[simp] def RelTwoElements (s t : α) (n : ℕ ) : F := (FreeGroup.mk [(s,true),(t,true)])^n 


@[simp] def toRelation'  (s : α × α ) : F :=
RelTwoElements s.1 s.2 (m.m s.1 s.2) 
-- (FreeGroup.mk [(s.1,true), (s.2, true)])^(m.m s.1 s.2)


def toRelationSet : (Set F):= 
Set.image (toRelation' m) Set.univ   
#check toRelationSet


def toGroup := PresentedGroup (m.toRelationSet) 

local notation "N" => Subgroup.normalClosure m.toRelationSet 
local notation "G" => m.toGroup  

instance : Group m.toGroup := QuotientGroup.Quotient.group _ 

/-
-- Coxeter group is a quotient group 
example :  m.toGroup = (F ⧸ N)  := by rfl
-/

def of (x : α) : G :=
QuotientGroup.mk' N (FreeGroup.of x) 

-- The set of simple reflections
def S := Set.image (m.of) Set.univ

end CoxeterMatrix


section CoxeterGroup

class hasOrderTwoGenerator (G: Type _) extends Group G where 
   S : Set G
   orderTwo: ∀ s ∈ S, s * s = 1  
   SgenG : Subgroup.closure S =  G

section mulList
variable {G: Type _} {G : Type _} [Group G]

def mulList  : (L : List G) -> G  
  | [] =>  1
  | x :: xs => x * (mulList xs) 

lemma mulListMul {L1 L2 : List G} : (mulList L1) * (mulList L2)
 = mulList (L1++L2) := sorry 


end  mulList 

/-
def Length {G: Type _} [Group G] [hasOrderTwoGenerator G] :=  
-/
/-
class CoxeterGroup (G : Type _) extends Group G where 
   S : Set G
   SgenG : Subgroup.closure S =  G

-/

end CoxeterGroup
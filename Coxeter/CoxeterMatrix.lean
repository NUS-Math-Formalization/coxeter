import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic


open Classical


universe u1 u2 u3

variable {α: Type u1}  {β: Type u2}  

@[ext,class] structure CoxeterMatrix (α : Type u1):= 
(m : Matrix α α ℕ)
(isSymm : ∀ (a b : α ), m a b = m b a )
(one_iff: ∀  {a b : α}, (m a b = 1) ↔ (a=b) )

instance : CoeFun (@CoxeterMatrix α) (fun _ => α -> α -> ℕ) where
   coe m := m.m 

#check CoxeterMatrix
namespace CoxeterMatrix 

variable (m : CoxeterMatrix α)

lemma Diag_is_one {s : α} : m.m s s = 1 := by
   rw [m.one_iff]


@[simp] def RelTwoElements (s t : α) (n : ℕ ) : FreeGroup α  := (FreeGroup.mk [(s,true),(t,true)])^n 


@[simp] def toRelation'  (s : α × α ) : FreeGroup α  :=
RelTwoElements s.1 s.2 (m s.1 s.2) 
-- (FreeGroup.mk [(s.1,true), (s.2, true)])^(m.m s.1 s.2)


def toRelationSet : (Set (FreeGroup α)):= 
Set.image (toRelation' m) Set.univ   
#check toRelationSet

def N := Subgroup.normalClosure (m.toRelationSet)  

instance : Subgroup.Normal m.N := Subgroup.normalClosure_normal

def toGroup := PresentedGroup (m.toRelationSet) 

instance : Group m.toGroup := QuotientGroup.Quotient.group _ 

lemma isQuotient:  m.toGroup = (FreeGroup α  ⧸ m.N)  := by rfl


def of (x : α) : m.toGroup := QuotientGroup.mk' (m.N) (FreeGroup.of x) 

-- The set of simple reflections
@[simp]
def S := Set.range (m.of) 

@[simp]
def alpha_to_S (a : α) : ↑ m.S := ⟨m.of a, by norm_num⟩       

end CoxeterMatrix




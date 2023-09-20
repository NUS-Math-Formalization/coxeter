
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic

--set_option profiler true
--set_option pp.all true
set_option synthInstance.maxHeartbeats 20000 -- default is 20000; five times that not enough here
set_option trace.Meta.synthInstance true

open Classical

/-
namespace FreeGroup

instance group: Group (FreeGroup α) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc := by rintro ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp
  one_mul := by rintro ⟨L⟩; rfl
  mul_one := by rintro ⟨L⟩; simp [one_eq_mk]
  mul_left_inv := by
    rintro ⟨L⟩
    exact
      List.recOn L rfl fun ⟨x, b⟩ tl ih =>
          Eq.trans (Quot.sound <| by simp [invRev, one_eq_mk]) ih


end FreeGroup 
-/

universe u1 u2 

variable {α: Type u1}  {β: Type u2}  

@[ext,class] structure CoxeterMatrix (α : Type u1):= 
(m : Matrix α α ℕ)
(isSymm : ∀ (a b : α ), m a b = m b a )
(one_iff: ∀  {a b : α}, m a b = (1 : ℕ) ↔ a=b )

instance : CoeFun (CoxeterMatrix α) (fun _ => α -> α -> ℕ) where
   coe m := m.m 

--coe ??

#check CoxeterMatrix
namespace CoxeterMatrix 

variable (m : CoxeterMatrix α)

lemma Diag_is_one {s : α} : m.m s s = (1 : ℕ)  := by
   rw [m.one_iff]


@[simp] 
def RelTwoElements (s t : α) (n : ℕ ) : FreeGroup α := HPow.hPow (FreeGroup.mk [(s,true),(t,true)]) n 


--def F (m : CoxeterMatrix α):= FreeGroup α
--instance : Group (m.F) := FreeGroup.group

@[simp] 
def toRelation'  (s : α × α ) : FreeGroup α :=
RelTwoElements s.1 s.2 (m s.1 s.2) 
-- (FreeGroup.mk [(s.1,true), (s.2, true)])^(m.m s.1 s.2)


def toRelationSet : (Set (FreeGroup α)):= 
Set.image (toRelation' m) Set.univ   
#check toRelationSet


def toGroup := PresentedGroup (m.toRelationSet) 


def N := Subgroup.normalClosure (m.toRelationSet)  

instance : Subgroup.Normal m.N := Subgroup.normalClosure_normal

instance : Group m.toGroup := QuotientGroup.Quotient.group _ 

/-
-- Coxeter group is a quotient group 
example :  m.toGroup = (F ⧸ N)  := by rfl
-/

def of (x : α) : m.toGroup :=
QuotientGroup.mk' (m.N) (FreeGroup.of x : FreeGroup α) 

-- The set of simple reflections
@[simp]
def S := Set.range (m.of) 

@[simp]
def alpha_to_S (a : α) :  ↑ m.S := ⟨m.of a, by norm_num⟩       

end CoxeterMatrix



variable {G : Type u3} [Group G] 

structure CoxeterGroup1 (S : Set G) where
 m : CoxeterMatrix  ↑S
 

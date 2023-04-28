import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Coxeter.Aux

open Classical

universe u1 u2 u3

variable {α: Type u1}  {β: Type u2}

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
/-
instance {S : Set G}: Coe (List S) (List G) where 
   coe L := List.map Coe L 
def CoeSubset {S : Set G}  (a : (↑S : Type _)) :  G := ↑a  
def CoeSubsetList {S : Set G} : (L : List (↑S : Type _)) -> (List G) := List.map CoeSubset  

#check CoeSubsetList

instance {S : Set G} : Coe (List (↑S : Sort) ) (List G) where 
   coe := CoeSubsetList   

-/




class HOrderTwoGenerator {G: Type _} [Group G] (S : Set G) : Prop where 
   orderTwo: ∀ {s : G }, s∈S → s * s = 1  
   SgenG : ∀ g :G , g ∈ Subgroup.closure S


section Length 

variable {G : Type _} {S : Set G} [Group G] [HOrderTwoGenerator S] 


lemma s_eq_inv_s {s : G}: s ∈ S → s = s⁻¹ := by { 
   intro hs
   have s2 := S _ hs 
   rw [<- mul_eq_one_iff_eq_inv] 

} 


lemma S_eq_InnSymm {s : G}: s ∈ (HOrderTwoGenerator.S) ↔ s ∈ InvSymm (HOrderTwoGenerator.S) := by { 
   apply Iff.intro
   have s2 : s *s  = 1 := HOrderTwoGenerator.orderTwo 
} 

def length_aux : ∃ (n:ℕ) , ∃ (L : List G),
   (∀ a ∈ L , a ∈ HOrderTwoGenerator.S )∧ L.length = n ∧ x = L.prod  
   := by {
   have hx := memClosure_iff_Prod.1 (HOrderTwoGenerator.SgenG x)
   let ⟨L, HL⟩ := hx
   use L.length  
   use L
   exact ⟨HL.1,by norm_num, HL.2⟩  
}  

/-
def length_aux {S : Set G} (H : ∀ x:G, x ∈ Subgroup.closure S) (x : G) : ∃ (n:ℕ) , ∃ (L : List G), 
   (∀ a∈ L , a ∈ InvSymm S )∧ L.length = n ∧ x = L.prod  
   := by {
   have hx := memClosure_iff_Prod.1 (H x)
   let ⟨L, HL⟩ := hx
   use L.length  
   use L
   exact ⟨HL.1,by norm_num, HL.2⟩  
}  
-/

end Length


end CoxeterGroup
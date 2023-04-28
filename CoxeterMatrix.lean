import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic


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

class HOrderTwoGenerator (G: Type u3) extends Group G where 
   S : Set G
   orderTwo: ∀ s ∈ S, s * s = 1  
   SgenG : Subgroup.closure S =  G

/-
section mulList
variable {G: Type u3}  [Monoid G] 

@[simp]
def mulList  : (L : List G) -> G  
  | [] =>  1
  | x :: xs => x * (mulList xs) 

@[simp]
lemma mulListMul {L1 L2 : List G} : (mulList L1) * (mulList L2)
 = mulList (L1++L2) := by 
   induction' L1 with hd tl H
   . simp
   . rw [mulList,mul_assoc,H,<-mulList] 
     congr 

end  mulList 
-/ 

section length
variable {G : Type u3} [Group G]

/-
instance {S : Set G}: Coe (List S) (List G) where 
   coe L := List.map Coe L 
def CoeSubset {S : Set G}  (a : (↑S : Type _)) :  G := ↑a  
def CoeSubsetList {S : Set G} : (L : List (↑S : Type _)) -> (List G) := List.map CoeSubset  

#check CoeSubsetList

instance {S : Set G} : Coe (List (↑S : Sort) ) (List G) where 
   coe := CoeSubsetList   

-/
@[simp]
def subsetList (S: Set G) : (Set (List G)) := 
{ L | ∀ a∈ L , a ∈ S}

@[simp]
def ProdGen (S : Set G) := Set.image List.prod (subsetList S) 

variable  [HOrderTwoGenerator G] 
variable (S: Set G)

lemma SsubProdGen  : S ⊆ ProdGen S := by 
{
   intro a ha
   rw [ProdGen,subsetList,Set.mem_image] 
   use [a] 
   simp [ha] 
} 

@[simp]
def eqSubsetProd (g : G) (S : Set G) := ∃ (L : List G), (∀ a∈L, a∈ S) ∧ g = L.prod 

@[simp]
def isInvSymm (S : Set G) := ∀ a ∈ S, a⁻¹ ∈ S 

@[simp] 
def InvSymm (S : Set G) := {a:G | a∈ S ∨ a⁻¹ ∈ S}

lemma eqInvSymm (S : Set G)  (H : isInvSymm S) : S = InvSymm S := by {
   rw [InvSymm]
   ext x
   rw [isInvSymm] at H
   constructor 
   { intro hx 
     simp [hx]}
   {
     intro hx
     apply Or.elim hx 
     simp  
     intro hxx
     have hxx := H x⁻¹ hxx
     simp at hxx
     exact hxx
   }
} 



lemma memClosureInvSymm (S : Set G) : InvSymm S ⊆ Subgroup.closure S:= by 
{
  rw [InvSymm]
  have HH : S ⊆ Subgroup.closure S := Subgroup.subset_closure 
  intro x hx 
  exact hx.elim (fun hxa => HH hxa) (fun hxb => by {
   apply (Subgroup.inv_mem_iff _).1
   exact HH hxb
  }) 
} 

lemma memProdInvSymm (S : Set G) (L : List G) (H : L∈ subsetList (InvSymm S)) : L.prod ∈ Subgroup.closure S := by {
   apply list_prod_mem
   intro x hx
   rw [subsetList] at H
   have := H x hx 
   exact (memClosureInvSymm S this)
} 

lemma memClosure_if_Prod {g : G} {S : Set G} : g ∈ Subgroup.closure S →  eqSubsetProd g (InvSymm S) := sorry 

lemma memClousre_iff_Prod {g : G} {S : Set G} : g ∈ Subgroup.closure S ↔ eqSubsetProd g (InvSymm S) := by 
{
   constructor 
   .  exact memClosure_if_Prod
   . {
    rw [eqSubsetProd, ] 
    intro ⟨L, HLa, HLb⟩ 
    rw [HLb] 
    apply memProdInvSymm _ _ HLa
   }
}  

-- lemma mulListGenerats  : S ⊂ ProdGen S

end length
/-
def Length {G: Type _} [Group G] [hasOrderTwoGenerator G] :=  
-/
/-
class CoxeterGroup (G : Type _) extends Group G where 
   S : Set G
   SgenG : Subgroup.closure S =  G

-/

end CoxeterGroup
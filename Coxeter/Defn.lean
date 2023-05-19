import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic

import Coxeter.Length

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

local notation  "F" => FreeGroup α

@[simp] def RelTwoElements (s t : α) (n : ℕ ) : F := (FreeGroup.mk [(s,true),(t,true)])^n 


@[simp] def toRelation'  (s : α × α ) : F :=
RelTwoElements s.1 s.2 (m s.1 s.2) 
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
@[simp]
def S := Set.range (m.of) 

@[simp]
def alpha_to_S (a : α) : ↑ m.S := ⟨m.of a, by norm_num⟩       

end CoxeterMatrix




variable {G : Type _} {A : Type _} [Group G] [SetLike A G] {S : A} 



section CoxeterGroup

section ExchangeDeletion

variable [orderTwoGen S]

local notation:max "ℓ(" g ")" => (@length G A _ _ S _ g)   

@[simp]
def exchangeProp :=
   ∀ {L : List S} {s : S },
     reduced_word L →  
      ℓ((s * L.gprod)) < ℓ(L.gprod) → ∃ (i: Fin L.length) ,s * L.gprod = (L.removeNth i).gprod


@[simp]
def deletionProp := 
    ∀ {L : List S}, 
    ℓ(L.gprod) < L.length → 
    ∃ (j: Fin L.length), ∃ (i:Fin j), L.gprod = ((L.removeNth j).removeNth i).gprod
   

lemma exchange_imp_deletion : @exchangeProp G A _ _ S _→ @deletionProp G A _ _ S _:= by {
   rw [exchangeProp,deletionProp]
   sorry  
   }


lemma deletion_imp_exchange : @deletionProp G A _ _ S _ → 
@exchangeProp G A _ _ S _ := by {
   sorry
}


end ExchangeDeletion


instance {G : Type _} : SetLike (Set G) G :=
{
   coe := id
   coe_injective' := by {
     intro a b hab 
     assumption 
   } 
}

class CoxeterGroup (G : Type _ ) {A : Type _} [Group G] [SetLike A G]  (S: A) where 
   m : @CoxeterMatrix S
   ι : m.toGroup ≃* G 
   ιid : ∀ (x : S), ι (m.alpha_to_S x) =  x  
   order_two : @orderTwoGen G A _ _ S  
   exchange : @exchangeProp G A _ _ S _  
   deletion : @deletionProp G A _ _ S _ 

instance {G : Type _} [CoxeterGroup G] : Group G := by {
   sorry
}
#check @length

#check CoxeterGroup.setlike

def CoxeterGroup.length (G : Type _) [h : CoxeterGroup G]:= @length G h.A   _ _ h.setlike 

namespace CoxeterGroup



end CoxeterGroup

import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Coxeter.Aux

open Classical

open Function

universe u1 u2 u3

variable {α: Type u1}  {β: Type u2}  

@[ext,class] structure CoxeterMatrix {α : Type u1}:= 
(m : Matrix α α ℕ)
(isSymm : ∀ (a b : α ), m a b = m b a )
(one_iff: ∀  {a b : α}, (m a b = 1) ↔ (a=b) )

instance : CoeFun (@CoxeterMatrix α) (fun _ => α -> α -> ℕ) where
   coe m := m.m 

#check CoxeterMatrix
namespace CoxeterMatrix 

variable (m : @CoxeterMatrix α)

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

lemma injS : Injective m.alpha_to_S := by {
   rw [Injective]  
   sorry 
} 

lemma surS : Surjective m.alpha_to_S := by {
   rw [Surjective] 
   intro b
   let ⟨y, hy⟩ :=b.2
   use y
   simp [hy]
}

lemma bijS : Bijective m.alpha_to_S := ⟨m.injS, m.surS⟩    


lemma order_eq_m (s s' : α) : orderOf ((m.of s) * (m.of s')) = m.m s s' := by sorry   



#check Equiv.ofBijective 

noncomputable def ιS : α ≃ m.S := Equiv.ofBijective m.alpha_to_S m.bijS 




/-
lemma injS  (x y : α) : x=y ↔ m.of x=m.of y := by {
   apply Iff.intro
   . intro; congr
   . {sorry}
}   

noncomputable def ιS [Nonempty α] : α ≃  m.S := {
   toFun := m.alpha_to_S,
   invFun := Function.invFun m.alpha_to_S,
   left_inv := @Function.leftInverse_invFun _ _ _ m.alpha_to_S m.injS ,
   right_inv := @Function.rightInverse_invFun _ _ _ m.alpha_to_S m.surS 
}
-/ 

end CoxeterMatrix

section Length
open Subgroup

variable {G : Type} [Group G] (S : Set G)

/-
class HOrderTwoGenClass (A : Type _) (G : Type _) [Group G] [SetLike A G] : Prop where 
   order_two: ∀ {x : G} {S:A}, x∈ S → x * x = 1  
   gen :  ∀ {S:A} (g :G), g ∈ Subgroup.closure S 
-/

def OrderTwoSet := ∀ s : G, s ∈ S →  s * s=1 


def isGeneratorSet := ∀ g : G, g ∈ Subgroup.closure S 


lemma s_eq_inv_s  {s : G} (H : OrderTwoSet S) : s ∈ S → s = s⁻¹ := by { 
   intro hs
   have s2 := H s hs  
   rw [<- mul_eq_one_iff_eq_inv,s2] 
} 


lemma s_eq_inv_s' {s : G} (H : OrderTwoSet S) : s⁻¹ ∈ S → s = s⁻¹ := by 
   {
      intro h
      have := s_eq_inv_s S H h 
      rw [this] 
      norm_num 
   } 

lemma S_eq_InnSymm {s : G} (H: OrderTwoSet S): s ∈ S ↔ s ∈ InvSymm S := by { 
   apply Iff.intro
   . { exact mem_InvSymm _} 
   . {
      intro h
      apply h.elim 
      . simp
      . { 
         intro hs 
         rw [s_eq_inv_s' S H hs]
         exact hs
       } 
   }    
} 

variable {G: Type _} [Group G] (S : Set G) (order_two: OrderTwoSet S) (gen: isGeneratorSet S) 

def length_aux_prop (x : G) (n :ℕ) := ∃ (L : List G),  
   (∀ a ∈ L , a ∈ S )∧ L.length = n ∧ x = L.prod  

def length_aux (x : G) : ∃ (n:ℕ) , ∃ (L : List G),
   (∀ a ∈ L , a ∈ S ) ∧ L.length = n ∧ x = L.prod  
   := by {
   have hx := memClosure_iff_Prod.1 (gen x)  
   let ⟨L, HL⟩ := hx
   use L.length  
   use L
   exact ⟨by { intro a ha 
               have := HL.1 a ha 
               rw [S_eq_InnSymm]
               exact this 
               exact order_two 
            },
          by norm_num, HL.2⟩  
} 

#check length_aux 

noncomputable def length (x : G) : ℕ := Nat.find (@length_aux G _ S order_two gen x) 

#check Nat.find_le
#check length_aux



lemma length_is_min (L : List G)  (h : L ∈ subsetList S):   
  @length G _ S order_two gen L.prod ≤ L.length :=  by {
  -- have HS := @length_aux _ _ S order_two gen L.prod  
  apply @Nat.find_le L.length (length_aux_prop S L.prod)  
  use L 
  exact ⟨h,rfl,rfl⟩ 
} 

@[simp]
def reduced_word (L : List G) := (L ∈ subsetList S) ∧ 
 ∀ (L' : List G), L'∈ subsetList S → L.prod =  L'.prod →  L.length ≤ L'.length


lemma nil_is_reduced_word: reduced_word S ([] : List G) 
:= by {
   exact ⟨nil_in_subsetList ,by {rintro _ _ _ ;norm_num}⟩  
} 




lemma length_le_reduced_words_iff (L: List G) (h: L ∈ subsetList S) : 
   reduced_word S L  ↔   L.length ≤ @length G _ S order_two gen L.prod:= by { 
      rw [length, (Nat.le_find_iff _)]
      apply Iff.intro
      . { 
         intro h m hm 
         rw [not_exists]
         intro LL 
         rw [not_and] 
         intro HLL 
         rw [not_and]
         contrapose 
         intro H
         simp at H 
         have HH := h.2 LL HLL H    
         apply Ne.symm
         apply ne_of_lt
         apply lt_of_lt_of_le hm HH 
       }
      . {
         intro H    
         rw [reduced_word] 
         exact ⟨h, by {
            intro LL HLa HLb 
            contrapose H 
            simp at H
            rw [not_forall] 
            use LL.length 
            rw [<-not_and,not_not] 
            constructor 
            . exact H 
            . {
               use LL 
               exact ⟨HLa,rfl,HLb⟩ 
            }   
         }⟩   
      }
   }

lemma length_eq_reduced_words_iff (L: List G) (h: L ∈ subsetList S) : 
   reduced_word S L  ↔   L.length = length S order_two gen L.prod:= by  
{
   apply Iff.intro
   . {
     intro H 
     exact ge_antisymm  (length_is_min S order_two gen L h)  ((length_le_reduced_words_iff S order_two gen L h).1 H)
   }
   . {
     intro H 
     exact (length_le_reduced_words_iff S order_two gen L h).2 (le_of_eq H)     
   }
}


lemma one_length_zero : length S order_two gen (1 : G) = 0 := by {
   have h:= (length_eq_reduced_words_iff S order_two gen [] (by simp)).1 (nil_is_reduced_word S) 
   simp at h
   rw [h]
} 

end Length



section CoxeterGroup


variable  {G : Type _} [Group G] (S : Set G) {order_two : OrderTwoSet S} {gen: isGeneratorSet S} 



def exchangeProp (S : Set G) (order_two : OrderTwoSet S) (gen: isGeneratorSet S):=
   ∀ (L : List G) {s : G } 
     (Hred : reduced_word S L ) (Hs : s ∈ S), 
      ((length S order_two gen (s * L.prod)) < length S order_two gen (L.prod)) → ∃ (i: Fin L.length) ,s * L.prod = (L.removeNth i).prod

def deletionProp (S : Set G) (order_two : OrderTwoSet S) (gen: isGeneratorSet S) := 
    ∀ {L : List G} {H: L ∈ subsetList S}, 
    (length S order_two gen (L.prod) < L.length) → 
    ∃ (j: Fin L.length), ∃ (i:Fin j), L.prod = ((L.removeNth j).removeNth i).prod
   

lemma exchange_imp_deletion 
(S : Set G) (order_two : OrderTwoSet S) (gen: isGeneratorSet S) : exchangeProp S order_two gen → deletionProp S order_two gen:= by {sorry }


lemma deletion_imp_exchange 
(S : Set G) (order_two : OrderTwoSet S) (gen: isGeneratorSet S) : deletionProp S order_two gen → exchangeProp S order_two gen:= by {sorry }


#check (([3,2] : List ℕ ) : List ℚ) 


@[class]
structure CoxeterGroup (G : Type _) extends Group G where 
   S : Set G 
   m : @CoxeterMatrix (↑S)
   ι: G ≃* m.toGroup 
   order_two : OrderTwoSet S 
   gen : isGeneratorSet S
   exchange : exchangeProp S order_two gen
   deletion : deletionProp S order_two gen 




end CoxeterGroup


section CoxeterMatrix


end CoxeterMatrix
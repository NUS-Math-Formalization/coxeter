import Mathlib.Tactic.Linarith
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Coxeter.Aux

open Classical

universe u1 u2 u3

variable {α: Type u1}  {β: Type u2}

@[ext,class] structure CoxeterMatrix {α : Type u1}:= 
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

section Length
open Subgroup



class HOrderTwoGenClass (A : Type _) (G : Type _) [Group G] [SetLike A G] : Prop where 
   order_two: ∀ {x : G} {S:A}, x∈ S → x * x = 1  
   gen :  ∀ {S:A} (g :G), g ∈ Subgroup.closure S 


def OrderTwoSet (S : Set G) [Group G] := ∀ s : G, s ∈ S →  s * s=1 


def GeneratorSet (S : Set G) [Group G] := ∀ g : G, g ∈ Subgroup.closure S 


variable {A : Type _ } {G: Type _} [Group G] [SetLike A G] [HOrderTwoGenClass A G] (S : A)

lemma s_eq_inv_s {s : G}: s ∈ S → s = s⁻¹ := by { 
   intro hs
   have s2 := HOrderTwoGenClass.order_two hs  
   rw [<- mul_eq_one_iff_eq_inv,s2] 
} 

--{A G} [Group G] [SetLike A G] [HOrderTwoGenClass A G] 
instance : InvMemClass A G :=  
  {inv_mem :=  by {
     intro S x hx 
     have := @s_eq_inv_s A G _ _ _ S ↑x hx 
     rw [<-this] 
     exact hx
   }
  }  

lemma s_eq_inv_s' {s : G}: s⁻¹ ∈ S → s = s⁻¹ := by 
   {
      intro h
      have := s_eq_inv_s _ h
      rw [this] 
      norm_num 
   } 

lemma S_eq_InnSymm {s : G}: s ∈ S ↔ s ∈ InvSymm S := by { 
   apply Iff.intro
   . { exact mem_InvSymm _} 
   . {
      intro h
      apply h.elim 
      . simp
      . { 
         intro hs 
         rw [s_eq_inv_s' _ hs]
         exact hs
       } 
   }    
} 

#check HOrderTwoGenClass.gen

def length_aux (x : G): ∃ (n:ℕ) , ∃ (L : List G),
   (∀ a ∈ L , a ∈ S )∧ L.length = n ∧ x = L.prod  
   := by {
   have in_closure:= @HOrderTwoGenClass.gen _ G _  _ _ S x    
   have hx := memClosure_iff_Prod.1 in_closure
   let ⟨L, HL⟩ := hx
   use L.length  
   use L
   exact ⟨by { intro a ha 
               have := HL.1 a ha 
               rw [S_eq_InnSymm ]
               exact this
            },
          by norm_num, HL.2⟩  
} 


noncomputable def length (x : G) : ℕ := Nat.find (length_aux S x) 

lemma length_is_min (L : List G)  (h : L ∈ subsetList S):  length S L.prod ≤ L.length :=  by {
  apply Nat.find_le 
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
   reduced_word S L  ↔   L.length ≤ length S L.prod:= by { 
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
   reduced_word S L  ↔   L.length = length S L.prod:= by  
{
   apply Iff.intro
   . {
     intro H 
     exact ge_antisymm  (length_is_min S L h)  ((length_le_reduced_words_iff S _ h).1 H)
   }
   . {
     intro H 
     exact (length_le_reduced_words_iff S _ h).2 (le_of_eq H)     
   }
}


lemma one_length_zero : length S (1 : G) = 0 := by {
   have h:= (length_eq_reduced_words_iff S [] (by simp)).1 (nil_is_reduced_word S) 
   simp at h
   rw [h]
} 


end Length


section CoxeterGroup

variable (A : Type _) (G : Type _) [Group G] [SetLike A G]

class HExchangePropClass  extends HOrderTwoGenClass A G  where 
   exchange: ∀ {S : A} {L : List G} {Hred: reduced_word S L} {s : G} (Hs: s ∈ S), 
    (length S (s * L.prod) < length S (L.prod)) → ∃ (i: Fin L.length) ,t * w = (L.removeNth i).prod



class HDeletionPropClass (A : Type _) (G : Type _) [Group G] [SetLike A G]  extends HOrderTwoGenClass A G  where 
   deletion: ∀ {S : A} {L : List G} {Hred: reduced_word S L}, 
    length S (L.prod) < L.length → 
    ∃ (j: Fin L.length), ∃ (i:Fin j), L.prod = ((L.removeNth j).removeNth i).prod


instance exchangeProp_imp_deletionProp [HExchangePropClass A G]: HDeletionPropClass A G := {
   deletion := by {
      intro S L Hred Hlen 
      sorry  
   },
}


instance deletionProp_imp_exchangeProp [HDeletionPropClass A G]: HExchangePropClass A G := {
   exchange:= by {
      intro S L Hred Hlen 
      sorry  
   },
}

/-
class HPresentationPropClass (A : Type _) (G : Type _) [Group G] [SetLike A G] extends HOrderTwoGenClass A G  where 
   m : ∀ {S : A} {L : List G} {Hred: reduced_word S L}, 
    length S (L.prod) < L.length → 
    ∃ (j: Fin L.length), ∃ (i:Fin j), L.prod = ((L.removeNth j).removeNth i).prod
-/

/-
@[coe]
def coe_list_mem {α : Type _ } {β : Type _} [Coe α β] (L : List α) : List β :=
List.map Coe.coe L
-/

--instance {α : Type _ } {β : Type _} [Coe α β] : Coe (List α) (List β) :=    

#check (([3,2] : List ℕ ) : List ℚ) 


class SimpleReflectionClass  (A : Type _) (G : Type _) [Group G] [SetLike A G]  extends
HOrderTwoGenClass A G, HExchangePropClass A G, HOrderTwoGenClass A G : Prop

@[class]
structure CoxeterGroup (A : Type _) (G : Type _) (G : Type _) [Group G] [SetLike A G]extends Group G where 
   S : A
   m : @CoxeterMatrix (↑S)
   props: SimpleReflectionClass A G
   ι: G ≃* m.toGroup 




end CoxeterGroup


section CoxeterMatrix


end CoxeterMatrix
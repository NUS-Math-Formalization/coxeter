import Coxeter.List
import Coxeter.Subgroup
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear


open Classical

variable  {G: Type _} {A : Type _} [Group G] [SetLike A G] {S : A}


class orderTwoGen (S : A):Prop  where 
  order_two :  ∀ (x:G) , x ∈ S →  x * x = (1 :G) ∧  x ≠ (1 :G)  
  generating : ∀ (x:G) , x ∈ Subgroup.closure S  

#check orderTwoGen

namespace orderTwoGen

lemma inv_eq_self  [orderTwoGen S]: ∀ x:G,  x∈S → x = x⁻¹ := 
fun x hx => mul_eq_one_iff_eq_inv.1 (order_two x hx).1



lemma non_one [orderTwoGen S]: ∀ x:G,  x∈S → x ≠ 1 := 
fun x hx => (order_two x hx).2


instance memInvMem  [orderTwoGen S]: Subgroup.InvMem S := 
{
  inv_mem := by {
    intro x hx
    rw [<- inv_eq_self x hx]
    exact hx
  }
}


lemma inv_eq_self'  [orderTwoGen S]: ∀ x:S,  x = x⁻¹ := 
by {
   intro x 
   ext 
   rw [inv_eq_self x.1 x.2]
   rfl
}

lemma eqSubsetProd [orderTwoGen S] (g : G) : ∃ (L : List S),  
   g = L.gprod := by {
    have H:= @generating G A _ _ S _ g   
    exact @Subgroup.memClosure_if_Prod G A _ _ S _ g H  
   }


end orderTwoGen

variable [orderTwoGen S]

def length_aux (g : G) : ∃ (n:ℕ) , ∃ (L : List S),
   L.length = n ∧ g = L.gprod  
   := by {
   have ⟨L, HL⟩   := @orderTwoGen.eqSubsetProd G A _ _  S _ g  
   use L.length  
   use L 
   --exact ⟨rfl,HL⟩  
} 


def length_aux_prop (g : G) (n :ℕ) := ∃ (L : List S),  
   L.length = n ∧ g = L.gprod  

noncomputable def length (x : G) : ℕ := Nat.find (@length_aux G A _ _ S _ x) 

local notation:max "ℓ(" g ")" => (@length G A _ _ S _ g)   


section Length

lemma length_is_min (L : List S) :   
  ℓ(L.gprod) ≤ L.length :=  by {
  -- have HS := @length_aux _ _ S order_two gen L.prod  
  apply @Nat.find_le L.length (length_aux_prop L.gprod)  
  use L 
  -- exact ⟨rfl,rfl⟩ 
} 


def reduced_word (L : List S) :=
∀ (L' : List S), L.gprod  = L'.gprod → L.length ≤ L'.length   


lemma nil_is_reduced_word: reduced_word ([] : List S) 
:= by {
   rintro _ _ 
   norm_num  
} 



lemma reduced_word_iff_length_le (L: List S) : 
   reduced_word L  ↔   L.length ≤ ℓ(L.gprod):= by { 
      rw [length, (Nat.le_find_iff _)]
      apply Iff.intro
      . { 
         intro h m hm 
         contrapose hm
         rw [not_not] at hm
         let ⟨L', HL'⟩ := hm  
         rw [not_lt,<-HL'.1]
         exact h L'  HL'.2    
       }
      . {
         intro H    
         rw [reduced_word] 
         intro L' HL' 
         contrapose H 
         rw [not_le] at H
         rw [not_forall] 
         use L'.length 
         rw [<-not_and,not_not] 
         constructor 
         . exact H 
         . {
            use L' 
            --exact ⟨rfl,HL'⟩ 
         }   
      }
   }


lemma reduced_word_iff_length_eq (L: List S) : 
   reduced_word L  ↔   L.length = ℓ(L.gprod) := by  
{
   constructor 
   . {
     intro H 
     exact ge_antisymm  (length_is_min L)  ((reduced_word_iff_length_le L).1 H)
   }
   . {
     intro H 
     exact (reduced_word_iff_length_le L).2 (le_of_eq H)     
   }
}



lemma one_length_zero : ℓ((1 : G)) = 0 := by {
   have h:= (reduced_word_iff_length_eq []).1 (@nil_is_reduced_word G A _ _ S) 
   simp at h
   rw [h]
} 



lemma reduced_word_exist (g : G) :∃ (L: List S) , reduced_word L ∧ g = L.gprod := by 
{
   let ⟨L',h1,h2⟩ := Nat.find_spec (@length_aux G A _ _ S _ g)
   use L'
   have C1 := (reduced_word_iff_length_eq L').2  
   rw [length] at C1
   simp_rw [h2] at h1
   exact ⟨C1 h1,h2⟩ 
}
variable (g:G)
#check reduced_word_exist g
#check List.map_id

lemma inv_reverse (L : List S) : L.gprod ⁻¹ = L.reverse.gprod := by {
   rw [Subgroup.inv_reverse_inv] 
   congr
   simp_rw [<-orderTwoGen.inv_eq_self']
   exact List.map_id L 
}

lemma inv_reverse' (L : List S) : L.gprod  = L.reverse.gprod ⁻¹ := inv_eq_iff_eq_inv.1 (inv_reverse L) 


lemma length_le_inv_length (g : G) : 
ℓ(g⁻¹)  ≤   ℓ(g)
:= by {
   have ⟨L, h1,h2⟩ := @reduced_word_exist G A _ _ S _ g
   have L1: L.length = ℓ(L.gprod) := (reduced_word_iff_length_eq L).1 h1
   rw [h2,<-L1]
   rw [inv_reverse,<-List.length_reverse L]  
   exact @length_is_min G A _ _ S _ L.reverse
}

lemma length_eq_inv_length (g : G) : 
ℓ(g⁻¹)  =   ℓ(g)
:= by {
    apply le_antisymm (length_le_inv_length g) 
    have gg : g⁻¹⁻¹ = g:= by {simp}
    have := @length_le_inv_length  G A _ _ S _ (g⁻¹) 
    rw [gg] at this 
    exact this
}


lemma reduced_word_inv (L: List S) : reduced_word L ↔ reduced_word L.reverse:=
by {
  repeat rw [reduced_word_iff_length_eq]
  rw [List.length_reverse,<-inv_reverse,length_eq_inv_length] 
}

end Length

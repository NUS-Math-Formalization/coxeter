import Coxeter.Basic

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.Linarith.Frontend


open Classical

variable {G: Type _} [Group G] (S : Set G) [orderTwoGen S] [CoxeterSystem G S]
local notation:max "ℓ(" g ")" => (@length G _ S _ g) 

lemma length_is_min (L : List S) :  ℓ(L.gprod) ≤ L.length := sorry




lemma reduced_word_inv (L: List S) (h: reduced_word L): reduced_word L.reverse:= sorry

lemma length_le_inv_length (g : G) : ℓ(g⁻¹)  ≤  ℓ(g) := sorry

lemma length_eq_inv_length (g : G) : ℓ(g⁻¹)  =  ℓ(g) := sorry

lemma nil_is_reduced_word: reduced_word ([] : List S) := by {
   rintro _ _ 
   norm_num  
} 

lemma pos_length_of_non_reduced_word (L : List S) 
: ¬ reduced_word L → 1 ≤  L.length := by {
   contrapose 
   simp_rw [not_le,not_not,Nat.lt_one_iff]
   rw [List.length_eq_zero];
   intro H
   simp only [H,nil_is_reduced_word] 
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
     exact ge_antisymm  (length_is_min S L)  ((reduced_word_iff_length_le S L).1 H)
   }
   . {
     intro H 
     exact (reduced_word_iff_length_le S L).2 (le_of_eq H)     
   }
}



lemma one_length_zero : ℓ((1 : G)) = 0 := by {
   have h:= (reduced_word_iff_length_eq S []).1 (@nil_is_reduced_word G _ S _) 
   simp at h
   rw [h]
} 



lemma reduced_word_exist (g : G) :∃ (L: List S) , reduced_word L ∧ g = L.gprod := by 
{
   let ⟨L',h1,h2⟩ := Nat.find_spec (@length_aux G  _ S  g _)
   use L'
   have C1 := (reduced_word_iff_length_eq S L').2  
   rw [length] at C1
   simp_rw [h2] at h1
   exact ⟨C1 h1,h2⟩ 
}



def non_reduced_p  (L : List S) := fun k => ¬ reduced_word (L.take (k+1))

lemma max_reduced_word_index_aux (L: List S) (H : ¬ reduced_word L) : ∃ n, non_reduced_p S L n := by {
   use L.length
   rw [non_reduced_p,List.take_all_of_le (le_of_lt (Nat.lt_succ_self L.length))] 
   exact H
}  

noncomputable def max_reduced_word_index (L : List S) (H : ¬ reduced_word L):= Nat.find (max_reduced_word_index_aux S L H) 

lemma nonreduced_succ_take_max_reduced_word (L : List S) (H : ¬ reduced_word L) : ¬ reduced_word (L.take ((max_reduced_word_index S L H)+1)) := by {
   let j:= max_reduced_word_index S L H
   have Hj : j = max_reduced_word_index S L H := rfl
   rw [<-Hj]
   rw [max_reduced_word_index]  at Hj
   have HH:= (Nat.find_eq_iff _).1 Hj
   rw [<-Hj,non_reduced_p] at HH
   exact HH.1
}

lemma reduced_take_max_reduced_word (L : List S) (H : ¬ reduced_word L) : reduced_word (L.take (max_reduced_word_index S L H)) := by {
   let j:= max_reduced_word_index S L H
   have Hj : j = max_reduced_word_index S L H := rfl
   match j with 
   | 0 =>  {
      rw [<-Hj,List.take_zero]
      exact nil_is_reduced_word S
    }
   | n+1 => {
      rw [<-Hj]
      have := (Nat.le_find_iff _ _).1 (le_of_eq Hj) n (Nat.lt_succ_self n)
      rw [non_reduced_p,not_not] at this
      exact this 
   } 
}


lemma length_lt_not_nil (L : List S) (s : S) : ℓ(L.gprod * s) < ℓ(L.gprod) → L ≠ [] := by {
   contrapose
   rw  [ne_eq, not_not, not_lt] 
   intro h
   rw [h,gprod_nil,one_length_zero] 
   exact zero_le (ℓ((1:G) * s))  
} 

lemma max_reduced_word_index_lt (L : List S) 
(H : ¬ reduced_word L) : max_reduced_word_index S L H < L.length := by {
   have Hlen := pos_length_of_non_reduced_word S L H
   rw [max_reduced_word_index, Nat.find_lt_iff _ L.length]
   use L.length -1 
   rw [non_reduced_p]
   have Hlen' : 0<L.length := by linarith
   constructor
   . exact Nat.sub_lt Hlen' (by simp)
   . {
      have : L.length -1 +1  = L.length := by rw [<-Nat.sub_add_comm Hlen,Nat.add_sub_cancel]
      rw [this,List.take_length]
      exact H
   }
} 

noncomputable def max_reduced_word_index' (L : List S) (H : ¬ reduced_word L) : Fin L.length:= ⟨max_reduced_word_index S L H, max_reduced_word_index_lt S L H⟩  

lemma length_lt_iff_non_reduced (L : List S) :
ℓ(L.gprod) < L.length ↔ ¬ reduced_word L := by {
   rw [iff_not_comm,not_lt]
   exact reduced_word_iff_length_le S L
} 



lemma reduced_nonreduced_length_le  (L : List S) (s:S) (H1: reduced_word L) (H2: ¬ reduced_word (L ++ [s])) : 
ℓ(L.gprod * s) ≤ ℓ(L.gprod) := by {
    rw [<-(reduced_word_iff_length_eq S L).1 H1]
    contrapose H2
    have Hs :[s].gprod = s := gprod_singleton
    have Hlen : (L++[s]).length = Nat.succ L.length := by rw [List.length_append, List.length_singleton] 
    rw [not_le,←gprod_singleton,←gprod_append,<-Nat.succ_le_iff,<-Hlen] at H2
    rw [not_not,reduced_word_iff_length_le S (L++[s])]
    exact H2
} 


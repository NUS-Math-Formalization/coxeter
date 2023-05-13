import Coxeter.Defn

open Classical 



section Length

open Subgroup

variable {G: Type _} [Group G] (S : Set G) (order_two: OrderTwoSet S) (gen: isGeneratorSet S) 



lemma reverse_prod_prod_eq_one (L: List G) (h : L ∈ subsetList S) : L.reverse.prod * L.prod = 1:= by {
  induction L with 
  | nil =>  {simp}
  | cons hd tail ih => {
    calc
(hd :: tail).reverse.prod  * (hd :: tail).prod
 =  tail.reverse.prod  * hd *(hd * tail.prod) := by simp
 _ =  List.prod (List.reverse tail) * (hd * hd * tail.prod):= by {
  rw [mul_assoc tail.reverse.prod, <-mul_assoc hd]} 
   _ =  tail.reverse.prod * tail.prod  := by { 
    have oo := order_two hd (cons_hd_subsetList S h)
    rw [oo]
    simp 
   }
   _ = 1 := ih  (cons_tail_subsetList S h) 
 }
} 

local notation:max "ℓ(" g ")" => (@length G _ S order_two gen g)   


lemma inv_eq_reverse_prod (L: List G) 
(h : L ∈ subsetList S) :
L.reverse.prod = (L.prod)⁻¹
:=  
mul_eq_one_iff_eq_inv.1 (reverse_prod_prod_eq_one S order_two  L h)


lemma reduced_word_inv (L: List G) (h: reduced_word S L): reduced_word  S L.reverse:=
by {
  rw [reduced_word]
  rw [reduced_word] at h 
  constructor 
  . {} 


  intros L''

}

lemma length_le_inv_length (g : G) : 
ℓ(g⁻¹)  ≤   ℓ(g)
:= by {
   have ⟨L, hh, h1, h2⟩ := reduced_word_exist S order_two gen g
   have L1: L.length = ℓ(L.prod) := (length_eq_reduced_words_iff S order_two gen L hh).1 h1
   rw [h2,<-L1]
  
}

end Length
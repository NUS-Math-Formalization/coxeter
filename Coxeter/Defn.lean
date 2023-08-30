import Mathlib.Tactic.Simps.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Logic.Relation

import Coxeter.List
import Coxeter.CoxeterMatrix 
import Coxeter.Length


--set_option trace.Meta.Tactic.simp.rewrite true 


open Classical


universe u1 u2 u3

section ExchangeDeletion


variable {G : Type _} {A : Type _} [Group G] [SetLike A G] (S : A) [HS : orderTwoGen S]

local notation:max "ℓ(" g ")" => (@length G A _ _ S _ g)   

@[simp]
def exchangeProp :=
   ∀ {L : List S} {s : S },
     reduced_word L →  
      ℓ((L.gprod * s)) ≤  ℓ(L.gprod) → ∃ (i: Fin L.length) , L.gprod * s= (L.removeNth i).gprod


@[simp]
def exchangeProp' :=
   ∀ {L : List S} {s : S },
     reduced_word L →  
      ℓ((s * L.gprod)) ≤ ℓ(L.gprod) → ∃ (i: Fin L.length) ,s * L.gprod = (L.removeNth i).gprod


example {a b : G} : a⁻¹*b⁻¹=(b*a)⁻¹:= by simp only [mul_inv_rev]


--lemma removeNth_reverse (L:ℕ) : True := rfls


lemma echange_iff : exchangeProp S →  exchangeProp' S := by {
   rw [exchangeProp,exchangeProp']
   intro EP L s HL Hlen
   let Lr := L.reverse
   have HLr := (reduced_word_inv L).1 HL
   have Hlenr :ℓ(L.reverse.gprod * s)≤ ℓ(L.reverse.gprod) := by {
      rw [<-inv_reverse,orderTwoGen.inv_eq_self s.1 s.2, <-(mul_inv_rev (↑s) (L.gprod))]
      rw [length_eq_inv_length,length_eq_inv_length] 
      exact Hlen 
   }
   let ⟨i, Hp⟩  := EP HLr Hlenr  
   rw [<-inv_reverse,orderTwoGen.inv_eq_self s.1 s.2,<-mul_inv_rev (↑s) (L.gprod)] at Hp
   let j : Fin L.length:= ⟨L.length -1 - i.1, by {
      sorry 
   }⟩    
   use j 
   sorry

} 



@[simp]
def deletionProp := 
    ∀ {L : List S}, 
    ℓ(L.gprod) < L.length → 
    ∃ (j: Fin L.length), ∃ (i: Fin j), L.gprod = ((L.removeNth j).removeNth i).gprod

lemma zero_or_one_of_lt_two {n : ℕ} : n< 2 ↔ n=0 ∨ n=1 := by 
match n with 
| 0 => simp
| 1 => simp  
| n+2 => simp

lemma pos_length_of_non_reduced_word (L : List S) 
: ¬ reduced_word L → 1 ≤  L.length := by {
   contrapose 
   simp_rw [not_le,not_not,Nat.lt_one_iff]
   rw [List.length_eq_zero];
   intro H
   simp only [H,nil_is_reduced_word] 
} 
/-
lemma not_reduced_word_of_length_ge (L : List S) 
: ¬ reduced_word L → 2 ≤  L.length := by {
   contrapose 
   simp_rw [not_le,not_not,zero_or_one_of_lt_two] 
   intro H
   cases H with 
   | inl h1 => {rw [List.length_eq_zero] at h1; simp only [h1,nil_is_reduced_word]} 
   | inr h2 => {rw [List.length_eq_one] at h2; let ⟨a,HL⟩:= h2  } 
} 
-/

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
      exact nil_is_reduced_word
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
   rw [h,Subgroup.nil_gprod,one_length_zero] 
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
   exact reduced_word_iff_length_le L
} 


--lemma max_reduced_word_index_gt (S:A) (L : List S) 
--(H : L ≠ [] ) : 1 ≤  max_reduced_word_index S L  H:= by sorry 

lemma reduced_nonreduced_length_le  (L : List S) (s:S) (H1: reduced_word L) (H2: ¬ reduced_word (L ++ [s])) : 
ℓ(L.gprod * s) ≤ ℓ(L.gprod) := by {
    rw [<-(reduced_word_iff_length_eq L).1 H1]
    contrapose H2
    have Hs :[s].gprod = s := Subgroup.gprod_singleton 
    have Hlen : (L++[s]).length = Nat.succ L.length := by rw [List.length_append, List.length_singleton] 
    rw [not_le,<-Subgroup.gprod_singleton,<-Subgroup.gprod_append,<-Nat.succ_le_iff,<-Hlen] at H2
    rw [not_not,reduced_word_iff_length_le (L++[s])]
    exact H2
} 


lemma exchange_imp_deletion : exchangeProp S → deletionProp S := by {
   rw [exchangeProp,deletionProp]
   intro EP L HL 
   have  HL' := (length_lt_iff_non_reduced S L).1 HL 
   let j := max_reduced_word_index' S L HL'
   use j
   let L1 := L.take j 
   have Hj : L1.length = j := List.take_le_length L (le_of_lt j.2) 
   have red_L1 : reduced_word L1 := reduced_take_max_reduced_word S L HL' 
   let s := L.get j 
   have nonred_L1p : ¬ reduced_word (L1++[s]) := by {
        rw [<-List.take_get_lt L j.1 j.2]
        have := nonreduced_succ_take_max_reduced_word S L HL'
        exact this
   } 
   have non_red_L1_s: ℓ((L1.gprod * s)) ≤  ℓ(L1.gprod) := reduced_nonreduced_length_le S L1 s red_L1 nonred_L1p 
   have ⟨i,HL1s⟩  := EP red_L1 non_red_L1_s 
   use ⟨i,(by {rw [<-Hj]; exact i.2})⟩ 
   rw [List.remove_nth_eq_take_drop L j] 
   have L1_ri : List.removeNth (L1 ++ L.drop (j+1)) i = L1.removeNth i ++ L.drop (j+1) := List.removeNth_append_lt L1 (L.drop (j+1)) i i.2  
   rw [L1_ri,Subgroup.gprod_append,<-HL1s,<-Subgroup.gprod_append_singleton, <-Subgroup.gprod_append]
   rw [<-List.take_drop_get L j]
   }


/-
def non_reduced_p  (L : List S)  :=  fun k => ¬ reduced_word (L.take k)    


def non_reduced_aux {L : List S} (h : ¬ reduced_word L) : ∃ n: ℕ, (@non_reduced_p G A _ _ S L n)   
:= by {
   use L.length
   rw [non_reduced_p,List.take_length]
   exact h
} 

noncomputable def min_non_reduced_index (L : List S) (h : ¬ reduced_word L) := @Nat.find (@non_reduced_p G A _ _ S L) _ (@non_reduced_aux G A _ _ S L h)   



lemma min_non_reduced_index_le_length {L : List S} {h : ¬ reduced_word L} : 0 < min_non_reduced_index S L h:= by {
  by_contra hh 
  rw [not_lt, nonpos_iff_eq_zero] at hh 
  rw [min_non_reduced_index, Nat.find_eq_iff] at hh
  have := hh.1 
  rw [non_reduced_p,List.take_zero] at this
  exact this nil_is_reduced_word 
}

lemma min_non_reduced_index_gt_zero {L : List S} {h : ¬ reduced_word L} : 0 < min_non_reduced_index S L h:= by {
  by_contra hh 
  rw [not_lt, nonpos_iff_eq_zero] at hh 
  rw [min_non_reduced_index, Nat.find_eq_iff] at hh
  have := hh.1 
  rw [non_reduced_p,List.take_zero] at this
  exact this nil_is_reduced_word 
}

lemma min_reduced_word {L : List S} {h : ¬ reduced_word L} : reduced_word (L.take  (min_non_reduced_index S L h -1)):= by {
   let k :=min_non_reduced_index S L h
   have hk : min_non_reduced_index S L h = k := by rfl
   rw [hk] 
   rw [min_non_reduced_index,Nat.find_eq_iff] at hk
}
-/

/-
lemma deletion_imp_exchange : deletionProp S → 
exchangeProp S := by {
   sorry
}

-/

end ExchangeDeletion

section Coxeter

variable {G : Type _} {A : Type _} [Group G]  [SetLike A G]  

-- #check orderOf 

class CoxeterSystem (S : A)  extends orderTwoGen S where 
   exchange: exchangeProp S  
   exchange': exchangeProp' S  
   deletion: deletionProp S
   --m : CoxeterMatrix S 
   --order_eq: ∀ (x y : S), orderOf ((x:G) * (y:G)) = m x y 


variable {S : A} [CoxeterSystem S]

local notation:max "ℓ(" g ")" => (@length G A _ _ S _ g)   

namespace CoxeterSystem


--def T :Set G := fun x => ∃ (w: G) (s : S),  x = w * (s : G) * w⁻¹
noncomputable def T: Set G := {x :G | ∃ (w: G) (s : S),   w * (s:G) * w⁻¹  = x}

local notation "TT" => (@T G A _ _ S)


@[simp]
def ltBt (x y) (t : TT) :=   (t:G) * x = y ∧ ℓ(x) < ℓ(y) 

@[simp]
def ltBone (x y : G) :=  ∃ (t : TT),  ltBt x y t

@[simp]
def ltB (x y : G) := Relation.TransGen (@ltBone G A _ _ S _)  x y 

def leB (x y : G) := x=y ∨ (@ltB G A _ _ S _ x y) 

local notation lhs:65 " <B  " rhs:65 => (@ltB G A _ _ S _  lhs rhs) 
local notation lhs:65 " ≤B  " rhs:65 => (@leB G A _ _ S _  lhs rhs) 

lemma trans (x y z:G) : x <B y → y <B z → x <B z := sorry  

end CoxeterSystem 
/-
namespace CoxeterSystem

variable (S : A) [CoxeterSystem S]

noncomputable def toCoxeterMatrix : CoxeterMatrix S := {
   m := fun x y => orderOf ((x:G) * (y:G))
   isSymm := sorry
   one_iff := sorry
} 

lemma iso_toGroup : (@toCoxeterMatrix G A _ _ S).toGroup ≃* G  := {
   toFun := sorry 
   invFun := sorry 
   left_inv := sorry 
   right_inv := sorry
   map_mul' := sorry
}


end CoxeterSystem

-/

end Coxeter

/-
-- Never uncomment this: 
-- It causes Lean overflow 

-/

/-
section Coxeter
variable {G : Type _} {A : Type _} [Group G] [SetLike A G]
 
class CoxeterGroup (S : A) where
 m : CoxeterMatrix S
 ι : m.toGroup ≃* G 
 ιid : ∀ (x : S), ι (m.alpha_to_S x) =  x  
 -/
/-
class CoxeterGroup (G : Type _ ) {A : Type _} [Group G] [SetLike A G]  (S: A) where 
   m : @CoxeterMatrix S
   ι : m.toGroup ≃* G 
   ιid : ∀ (x : S), ι (m.alpha_to_S x) =  x  
   order_two : @orderTwoGen G A _ _ S  
   exchange : @exchangeProp G A _ _ S _  
   deletion : @deletionProp G A _ _ S _ 

#check @length
-/

-- def CoxeterGroup.length (G : Type _) := @length G A   _ _ h.setlike 

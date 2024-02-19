import Coxeter.OrderTwoGen

namespace OrderTwoGen
variable {G : Type*} [Group G] (S : Set G) [OrderTwoGen S]

local notation:max "ℓ(" g ")" => (length S g)

def ExchangeProp := ∀ (L:List S) (s:S) ,reduced_word L →
      ℓ(s * L) ≤ ℓ(L) → ∃ (i: Fin L.length), (s :G) * L= (L.removeNth i)


def ExchangeProp' :=
   ∀ {L : List S} {s : S },
   reduced_word L → ℓ(( L * s)) ≤ ℓ(L) → ∃ (i: Fin L.length) ,(L:G) * s= (L.removeNth i)


lemma exchange'_if_exchange : ExchangeProp S →  ExchangeProp' S:= by {
   rw [ExchangeProp,ExchangeProp']
   intro EP L s HL Hlen
   let Lr := L.reverse
   have HLr := reverse_is_reduced  HL
   have Hlenr :ℓ(s * L.reverse)≤ ℓ(L.reverse) := by {
      calc
      _ =  ℓ((s * L.reverse)⁻¹) := length_eq_inv_length
      _ =  ℓ(L * s) := by {
         congr 1
         nth_rewrite 1 [gprod_reverse,inv_eq_self' s]
         group }
      _ ≤  ℓ(L) := Hlen
      _ =  ℓ(L.reverse) := by simp only [reverse_length_eq_length]
   }
   let ⟨i, Hp⟩  := EP Lr s HLr Hlenr
   rw [<-gprod_cons] at Hp
   let j : Fin L.length:= ⟨L.length -1 - i.1, by {
      have : (0:ℕ)  < L.length := by {

      calc
         (0:ℕ)  ≤ i := by simp
         _ < Lr.length := i.2
         _ = L.length := by simp
         }
      calc
      _ ≤  L.length - 1 := by linarith
      _ < _ := by simp [this]

      }
   sorry
   }⟩
   use j

   sorry
}



def DeletionProp := ∀ (L:List S), ℓ( L ) < L.length → ∃ (j: Fin L.length), ∃ (i:Fin j), (L:G)= ((L.removeNth j).removeNth i)


lemma exchange_imp_deletion : ExchangeProp S →  DeletionProp S := by {
   rw [ExchangeProp,DeletionProp]
   intro EP L HL
   have  HL' : ¬ reduced_word L := (length_lt_iff_non_reduced).1 HL
   let j := max_reduced_word_index' HL'
   use j
   let L1 := L.take j
   have Hj : L1.length = j := List.take_le_length L (le_of_lt j.2)
   have red_L1 : reduced_word L1 := reduced_take_max_reduced_word HL'
   let s := L.get j
   have nonred_L1p : ¬ reduced_word (L1++[s]) := by {
        rw [<-List.take_get_lt L j.1 j.2]
        have := nonreduced_succ_take_max_reduced_word  HL'
        exact this
   }
   have non_red_L1_s: ℓ((L1 * s)) ≤  ℓ(L1) := reduced_nonreduced_length_le red_L1 nonred_L1p
   -- have ⟨i,HL1s⟩  := EP L1 s red_L1 non_red_L1_s
   -- use ⟨i,(by {rw [<-Hj]; exact i.2})⟩
   -- rw [List.remove_nth_eq_take_drop L j]
   -- have L1_ri : List.removeNth (L1 ++ L.drop (j+1)) i = L1.removeNth i ++ L.drop (j+1) := List.removeNth_append_lt L1 (L.drop (j+1)) i i.2
   -- rw [L1_ri,Subgroup.gprod_append,<-HL1s,<-Subgroup.gprod_append_singleton, <-Subgroup.gprod_append]
   -- rw [<-List.take_drop_get L j]
   sorry
 }

/-
We now prove that ExchangeProp and DeletionProperty are equivalent
-/

end OrderTwoGen

class CoxeterSystem {G : Type _} [Group G] (S : Set G) extends OrderTwoGen S where
  exchange : OrderTwoGen.ExchangeProp S
  exchange' : OrderTwoGen.ExchangeProp' S := OrderTwoGen.exchange'_if_exchange S exchange
  deletion : OrderTwoGen.DeletionProp S

namespace CoxeterSystem

variable {G: Type*} [Group G] (S : Set G) [CoxeterSystem S]

end CoxeterSystem


-- structure expression where
-- element:G
-- reduced_expr:List S
-- reduced_property: reduced_word reduced_expr

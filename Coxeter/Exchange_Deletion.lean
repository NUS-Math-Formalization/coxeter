import Coxeter.Basic
import Coxeter.Length_reduced_word
import Coxeter.Auxi

variable {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S]

local notation:max "ℓ(" g ")" => (@length G _ S _ g)

@[simp]
def ExchangeProp' :=
   ∀ {L : List S} {s : S },
   reduced_word L → ℓ(( L.gprod * s)) ≤ ℓ(L.gprod) → ∃ (i: Fin L.length) ,L.gprod * s= (L.removeNth i).gprod

lemma zero_or_one_of_lt_two {n : ℕ} : n< 2 ↔ n=0 ∨ n=1 := by
match n with
| 0 => simp
| 1 => simp
| n+2 => simp

lemma exchange_iff : @ExchangeProp G _ S _ →  @ExchangeProp' G _ S _ := by {
   rw [ExchangeProp,ExchangeProp']
   intro EP L s HL Hlen
   let Lr := L.reverse
   have HLr := reduced_word_inv  L HL
   have Hlenr :ℓ(s * L.reverse.gprod)≤ ℓ(L.reverse.gprod) := by {
      -- rw [<-inv_reverse,orderTwoGen.inv_eq_self s.1 s.2, <-(mul_inv_rev (↑s) (L.gprod))]
      -- rw [length_eq_inv_length,length_eq_inv_length]
      -- exact Hlen
      sorry
   }
   let ⟨i, Hp⟩  := EP Lr s HLr Hlenr
   rw [<-gprod_cons] at Hp
   let j : Fin L.length:= ⟨L.length -1 - i.1, by {
      sorry
   }⟩
   use j
   sorry
}

lemma exchange_imp_deletion : @ExchangeProp G _ S _ →  @DeletionProp G _ S _ := by {
   rw [ExchangeProp,DeletionProp]
   intro EP L HL
   have  HL' := (length_lt_iff_non_reduced  L).1 HL
   let j := max_reduced_word_index'  L HL'
   use j
   let L1 := L.take j
   have Hj : L1.length = j := List.take_le_length L (le_of_lt j.2)
   have red_L1 : reduced_word L1 := reduced_take_max_reduced_word  L HL'
   let s := L.get j
   have nonred_L1p : ¬ reduced_word (L1++[s]) := by {
        rw [<-List.take_get_lt L j.1 j.2]
        have := nonreduced_succ_take_max_reduced_word  L HL'
        exact this
   }
   have non_red_L1_s: ℓ((L1.gprod * s)) ≤  ℓ(L1.gprod) := reduced_nonreduced_length_le  L1 s red_L1 nonred_L1p
   -- have ⟨i,HL1s⟩  := EP L1 s red_L1 non_red_L1_s
   -- use ⟨i,(by {rw [<-Hj]; exact i.2})⟩
   -- rw [List.remove_nth_eq_take_drop L j]
   -- have L1_ri : List.removeNth (L1 ++ L.drop (j+1)) i = L1.removeNth i ++ L.drop (j+1) := List.removeNth_append_lt L1 (L.drop (j+1)) i i.2
   -- rw [L1_ri,Subgroup.gprod_append,<-HL1s,<-Subgroup.gprod_append_singleton, <-Subgroup.gprod_append]
   -- rw [<-List.take_drop_get L j]
   sorry
 }

lemma deletion_imp_exchange : @DeletionProp G _ S _ → @ExchangeProp G _ S _ := sorry

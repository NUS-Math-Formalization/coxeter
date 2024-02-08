import Coxeter.OrderTwoGen

namespace OrderTwoGen
variable {G : Type*} [Group G] (S : Set G) [OrderTwoGen S]

local notation:max "ℓ(" g ")" => (length S g)

@[simp]
abbrev ExchangeProp := ∀ {L:List S} {s:S} ,reduced_word L →
      ℓ(s * L) ≤ ℓ(L) → ∃ (i: Fin L.length), (s :G) * L= (L.removeNth i)

@[simp]
abbrev  ExchangeProp' :=
   ∀ {L : List S} {s : S},
   reduced_word L → ℓ(( L * s)) ≤ ℓ(L) → ∃ (i: Fin L.length) ,(L:G) * s= (L.removeNth i)


lemma exchange_iff_exchange' : ExchangeProp S ↔   ExchangeProp' S:= by {
   constructor
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
   let ⟨i, Hp⟩  := EP HLr Hlenr
   rw [←gprod_cons] at Hp
   let j : Fin L.length:= ⟨L.length -1 - i.1, by {
      have : (0:ℕ)  < L.length := by {
      sorry
      /- calc
         (0:ℕ)  ≤ i := by simp
         _ < Lr.length := i.2
         _ = L.length := by simp
         }
      calc
      _ ≤  L.length - 1 := by sorry
      _ < _ := by sorry -/

      }
      sorry
    }⟩
   use j

   sorry
   sorry
}



def DeletionProp := ∀ (L:List S), ℓ( L ) < L.length → ∃ (j: Fin L.length), ∃ (i:Fin j), (L:G)= ((L.removeNth j).removeNth i)


/- lemma exchange_imp_deletion : ExchangeProp S →  DeletionProp S := by {
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
        rw [←List.take_get_lt L j.1 j.2]
        have := nonreduced_succ_take_max_reduced_word  HL'
        exact this
   }
   have non_red_L1_s: ℓ((L1 * s)) ≤  ℓ(L1) := reduced_nonreduced_length_le red_L1 nonred_L1p
   -- have ⟨i,HL1s⟩  := EP L1 s red_L1 non_red_L1_s
   -- use ⟨i,(by {rw [←Hj]; exact i.2})⟩
   -- rw [List.remove_nth_eq_take_drop L j]
   -- have L1_ri : List.removeNth (L1 ++ L.drop (j+1)) i = L1.removeNth i ++ L.drop (j+1) := List.removeNth_append_lt L1 (L.drop (j+1)) i i.2
   -- rw [L1_ri,Subgroup.gprod_append,←HL1s,←Subgroup.gprod_append_singleton, ←Subgroup.gprod_append]
   -- rw [←List.take_drop_get L j]
   sorry
 }
 -/
/-
We now prove that ExchangeProp and DeletionProperty are equivalent
-/

lemma take_drop_get' (L: List S) (n : ℕ) (h : n < L.length):
  L = (L.take n).gprod * [L.get ⟨n, h⟩] * L.drop (n+1) := by
  rw [←gprod_append, ←gprod_append]
  apply congr_arg
  exact List.take_drop_get L n h



lemma exchange_imp_deletion : ExchangeProp S →  DeletionProp S:= by
  rw [exchange_iff_exchange']
  rw [ExchangeProp', DeletionProp]
  intro EP' L HL
  have HL' := (length_lt_iff_non_reduced).1 HL
  let j := max_reduced_word_index' HL'; use j
  let L1 := L.take j; let s := L.get j
  have Hj : L1.length = j := List.take_le_length L (le_of_lt j.2)
  have red_L1 : reduced_word L1 := reduced_take_max_reduced_word HL'
  have non_red_L1p : ¬ reduced_word (L1 ++ [s]) := by
    rw [← List.take_get_lt L j.1 j.2]
    have := nonreduced_succ_take_max_reduced_word HL'
    exact this
  have non_red_L1_s: ℓ((L1.gprod * s)) ≤ ℓ(L1.gprod) := by
    apply reduced_nonreduced_length_le red_L1 non_red_L1p
  let ⟨i, Hp⟩ := EP' red_L1 non_red_L1_s
  have Hlen : i < j.1 := by rw [←Hj]; exact i.2
  let i_fin_j : Fin j := ⟨i, Hlen⟩; use i_fin_j
  have h_L_decomp : (List.removeNth (List.removeNth L j) i) =
    (List.removeNth L1 i).gprod * (List.drop (j+1) L) := by
    rw [←gprod_append]; apply congr_arg
    rw [←List.removeNth_append_lt, ←List.remove_nth_eq_take_drop]
    exact i.2
  rw [h_L_decomp, ←Hp, ←gprod_singleton]
  apply take_drop_get'



lemma deletion_imp_exchange : @DeletionProp G _ S _ → @ExchangeProp G _ S _ := by
  rw [exchange_iff_exchange']
  rw [ExchangeProp', DeletionProp]
  intro DP L s red_L h_len
  have h_len' : ℓ(L ++ [s]) < List.length (L ++ [s]) := by
    simp only [List.length_append, List.length_singleton]
    rw [gprod_append_singleton, (length_eq_iff).mp]
    linarith; assumption
  let ⟨j, i, h_dp⟩ := DP (L ++ [s]) h_len'

  -- To be simplified?
  have h_i_lt_kp1 : i < List.length (L ++ [s]) := by
    apply LT.lt.trans i.2 j.2
  have h_i_lt_k : i < L.length := by
    have := i.2
    have j_le_k : j.1 ≤ L.length := by
      apply Nat.le_of_lt_succ
      rw [Nat.succ_eq_add_one, ←List.length_append_singleton]
      exact j.2
    linarith

  let i' : Fin (L ++ [s]).length := ⟨i, h_i_lt_kp1⟩
  by_cases hs : s ≠ (L ++ [s]).get j ∧ s ≠ (L ++ [s]).get i'
  . exfalso

    -- To be simplified?
    have h_j_lt_k : j < L.length := by
      have j_le_k : j.1 ≤ L.length := by
        apply Nat.le_of_lt_succ
        rw [Nat.succ_eq_add_one, ←List.length_append_singleton]
        exact j.2
      have j_ne_k : j.1 ≠ L.length := by
        intro h; rw [←List.eq_last_index_of_get_last_singleton s] at h
        swap; exact j.2
        let hhh := hs.left
        have h' : s = List.get (L ++ [s]) j := by exact symm h
        exact hhh h'
      exact lt_of_le_of_ne j_le_k j_ne_k

     -- Automatically simplify?
    have h_i_lt_k' : i < (L.removeNth j).length := by
      rw [List.length_removeNth];
      have := i.2
      have j_le_km1 : j.1 ≤ L.length - 1 := by
        apply Nat.le_sub_one_of_lt
        exact h_j_lt_k;
      linarith; assumption

    have : (L ++ [s]).gprod = ((L.removeNth j).removeNth i) ++ [s] := by
      calc
        (L ++ [s]).gprod = ((L ++ [s]).removeNth j).removeNth i := by exact h_dp
        _ = (L.removeNth j ++ [s]).removeNth i := by
          rw [List.removeNth_append_lt L [s] j.1 h_j_lt_k]
        _ = (L.removeNth j).removeNth i ++ [s] := by
          rw [List.removeNth_append_lt (L.removeNth j) [s] i'.1 h_i_lt_k']

    have : L.gprod = (L.removeNth j).removeNth i := by
      rw [gprod_append_singleton, gprod_append_singleton] at this
      exact mul_right_cancel this

    -- Automatically simplify?
    have len_l_lt: ℓ(L) < List.length L := by
      rw [this]
      calc
        ℓ((L.removeNth j).removeNth i) ≤ ((L.removeNth j).removeNth i).length := by
          apply length_le_list_length
        _ = List.length L - 1 - 1 := by
          rw [List.length_removeNth, List.length_removeNth]
          assumption; assumption
        _ ≤ List.length L - 1 := by apply Nat.sub_le
        _ < List.length L := by sorry

    have : ℓ(L) = List.length L := by
      rw [length_eq_iff] at red_L
      apply symm; assumption
    rw [this] at len_l_lt
    exact lt_irrefl _ len_l_lt
  . push_neg at hs
    by_cases h_s_eq_j : s = (L ++ [s]).get j

    -- Automatically simplify?
    . have : (L ++ [s]).gprod = (L.removeNth i') := by
        calc
          (L ++ [s]).gprod = (((L ++ [s]).removeNth j).removeNth i').gprod := by exact h_dp
          _ = (L.removeNth i') := by rw [(List.eq_self_of_append_removeNth' s).mp (symm h_s_eq_j)]
      let i'' : Fin L.length := ⟨i, h_i_lt_k⟩; use i''
      rw [←gprod_append_singleton, this]
    . exfalso; push_neg at h_s_eq_j
      let h_s_eq_i' := hs h_s_eq_j
      have : i'.1  = L.length := by
        apply (List.eq_last_index_of_get_last_singleton s).mp
        exact symm h_s_eq_i'
      rw [this] at h_i_lt_k
      exact lt_irrefl _ h_i_lt_k

end OrderTwoGen

open OrderTwoGen

class CoxeterSystem {G : Type*} [Group G] (S : Set G) extends OrderTwoGen S where
  exchange : OrderTwoGen.ExchangeProp S
  exchange' : OrderTwoGen.ExchangeProp' S := (exchange_iff_exchange' S).1 exchange
  deletion : OrderTwoGen.DeletionProp S := exchange_imp_deletion S exchange

-- namespace CoxeterSystem

-- variable {G: Type*} [Group G] (S : Set G) [CoxeterSystem S]

-- end CoxeterSystem


-- structure expression where
-- element:G
-- reduced_expr:List S
-- reduced_property: reduced_word reduced_expr

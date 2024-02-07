import Coxeter.OrderTwoGen
import Coxeter.Length_reduced_word
import Coxeter.Auxi

variable {G : Type _} [Group G] {S :Set G} [OrderTwoGen S] [CoxeterSystem G S]

open OrderTwoGen

local notation:max "ℓ(" g ")" => (@length G _ S _ g)
open reduced_word

#check List.length_append_singleton
@[simp]
def ExchangeProp' :=
  ∀ {L : List S} {s : S },
  reduced_word L → ℓ((L.gprod * s)) ≤ ℓ(L.gprod) → ∃ (i: Fin L.length), L.gprod * s = (L.removeNth i).gprod

-- def ExchangeProp :=
--    ∀ (L : List S) (s : S),
--    reduced_word L → ℓ((s * L.gprod)) ≤ ℓ(L.gprod) → ∃ (i: Fin L.length), s * L.gprod = (L.removeNth i).gprod


-- lemma ExchangeProp_of_reflection (L : List S) : ∀


lemma zero_or_one_of_lt_two {n : ℕ} : n< 2 ↔ n=0 ∨ n=1 := by
  match n with
  | 0 => simp
  | 1 => simp
  | n+2 => simp


lemma exchange_iff : @ExchangeProp G _ S _ ↔  @ExchangeProp' G _ S _ := by sorry
  -- rw [ExchangeProp,ExchangeProp']
  -- intro EP L s HL Hlen
  -- let Lr := L.reverse
  -- have HLr := reduced_word.inv L HL
  -- have Hlenr :ℓ(s * L.reverse.gprod) ≤ ℓ(L.reverse.gprod) := by {
  --    rw [gprod_reverse, OrderTwoGen.inv_eq_self s.1 s.2, ←(mul_inv_rev (L.gprod) (↑s))]
  --    rw [←length_eq_inv_length, ←length_eq_inv_length]
  --    exact Hlen
  -- }
  -- let ⟨i, Hp⟩  := EP Lr s HLr Hlenr
  -- rw [←gprod_cons] at Hp
  -- let j : Fin L.length:= ⟨L.length -1 - i.1, by {
  --    sorry
  -- }⟩
  -- use j
  -- sorry

lemma take_drop_get' (L: List S) (n : ℕ) (h : n < L.length):
  L = (L.take n).gprod * [L.get ⟨n, h⟩] * L.drop (n+1) := by
  rw [←gprod_append, ←gprod_append]
  apply congr_arg
  exact List.take_drop_get L n h



lemma exchange_imp_deletion : @ExchangeProp G _ S _ →  @DeletionProp G _ S _ := by
  rw [exchange_iff]
  rw [ExchangeProp', DeletionProp]
  intro EP' L HL
  have HL' := (length_lt_iff_non_reduced L).1 HL
  let j := max_reduced_word_index' L HL'; use j
  let L1 := L.take j; let s := L.get j
  have Hj : L1.length = j := List.take_le_length L (le_of_lt j.2)
  have red_L1 : reduced_word L1 := reduced_take_max_reduced_word L HL'
  have non_red_L1p : ¬ reduced_word (L1 ++ [s]) := by
    rw [← List.take_get_lt L j.1 j.2]
    have := nonreduced_succ_take_max_reduced_word L HL'
    exact this
  have non_red_L1_s: ℓ((L1.gprod * s)) ≤ ℓ(L1.gprod) := by
    apply reduced_nonreduced_length_le L1 s red_L1 non_red_L1p
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
  rw [exchange_iff]
  rw [ExchangeProp', DeletionProp]
  intro DP L s red_L h_len
  have h_len' : ℓ(L ++ [s]) < List.length (L ++ [s]) := by
    simp only [List.length_append, List.length_singleton]
    rw [gprod_append_singleton, (reduced_word.length_eq_iff L).mp]
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
          apply reduced_word.length_le
        _ = List.length L - 1 - 1 := by
          rw [List.length_removeNth, List.length_removeNth]
          assumption; assumption
        _ ≤ List.length L - 1 := by apply Nat.sub_le
        _ < List.length L := by sorry

    have : ℓ(L) = List.length L := by
      rw [reduced_word.length_eq_iff] at red_L
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

import Coxeter.OrderTwoGen
import Coxeter.Aux_
import Mathlib.Data.Matrix.Basic

/-!
# A Characterization

In this file we define the `ExchangeProp` and `DeletionProp` for an `OrderTwoGen` group `G`.
We then prove that they are equivalent.
-/

namespace OrderTwoGen
variable {G : Type*} [Group G] (S : Set G) [OrderTwoGen S]

local notation : max "ℓ(" g ")" => (length S g)

@[simp]
abbrev ExchangeProp := ∀ {L : List S} {s : S}, reduced_word L →
  ℓ(s * L) ≤ ℓ(L) → ∃ (i : Fin L.length), (s : G) * L = L.removeNth i

@[simp]
abbrev ExchangeProp' := ∀ {L : List S} {s : S}, reduced_word L →
  ℓ(L * s) ≤ ℓ(L) → ∃ (i : Fin L.length), (L : G) * s = L.removeNth i

@[simp]
abbrev DeletionProp := ∀ (L : List S), ℓ(L) < L.length →
  ∃ (j : Fin L.length), ∃ (i : Fin j), (L : G) = (L.removeNth j).removeNth i

lemma exchange_iff_exchange' : ExchangeProp S ↔ ExchangeProp' S := by
  constructor
  · rw [ExchangeProp, ExchangeProp']
    intro EP L s h_red_L h_len
    have h_red_L_rev := reverse_is_reduced h_red_L
    have h_len_r : ℓ(s * L.reverse) ≤ ℓ(L.reverse) := by calc
      _ = ℓ((s * L.reverse)⁻¹) := length_eq_inv_length
      _ = ℓ(L * s) := by
        congr 1
        nth_rewrite 1 [gprod_reverse, inv_eq_self' s]
        group
      _ ≤ ℓ(L) := h_len
      _ = ℓ(L.reverse) := by simp only [reverse_length_eq_length]
    let ⟨i, Hp⟩ := EP h_red_L_rev h_len_r
    rw [← gprod_cons] at Hp
    have h_i_lt_k : i < L.length := by have := i.2; simp only [List.length_reverse] at this; exact this
    let j := L.length - i - 1
    have h_j_lt_k : j < L.length := by apply Nat.sub_sub_one_lt_self; exact Nat.pos_of_lt h_i_lt_k
    let j' : Fin L.length := ⟨j, h_j_lt_k⟩
    use j'
    rw [← gprod_append_singleton]
    apply eq_of_one_div_eq_one_div
    rw [← inv_eq_one_div, ← inv_eq_one_div, ← OrderTwoGen.gprod_reverse, ← OrderTwoGen.gprod_reverse, List.reverse_cons'']
    rw [List.removeNth_reverse L i h_i_lt_k] at Hp
    rw [Hp]
  rw [ExchangeProp, ExchangeProp']
  intro EP' L s h_red_L h_len
  have h_red_L_rev := reverse_is_reduced h_red_L
  have h_len_r : ℓ(L.reverse * s) ≤ ℓ(L.reverse) := by calc
    _ = ℓ((L.reverse * s)⁻¹) := length_eq_inv_length
    _ = ℓ(s * L) := by
      congr 1
      nth_rewrite 1 [gprod_reverse, inv_eq_self' s]
      group
    _ ≤ ℓ(L) := h_len
    _ = ℓ(L.reverse) := by simp only [reverse_length_eq_length]
  let ⟨i, Hp⟩ := EP' h_red_L_rev h_len_r
  rw [← gprod_append_singleton] at Hp
  have h_i_lt_k : i < L.length := by have := i.2; simp only [List.length_reverse] at this; exact this
  let j := L.length - i - 1
  have h_j_lt_k : j < L.length := by apply Nat.sub_sub_one_lt_self; exact Nat.pos_of_lt h_i_lt_k
  let j' : Fin L.length := ⟨j, h_j_lt_k⟩
  use j'
  rw [← gprod_cons]
  apply eq_of_one_div_eq_one_div
  rw [← inv_eq_one_div, ← inv_eq_one_div, ← OrderTwoGen.gprod_reverse, ← OrderTwoGen.gprod_reverse, List.reverse_cons]
  rw [List.removeNth_reverse L i h_i_lt_k] at Hp
  rw [Hp]

/-
We now prove that ExchangeProp and DeletionProperty are equivalent
-/
lemma exchange_imp_deletion : ExchangeProp S → DeletionProp S := by
  rw [exchange_iff_exchange']
  rw [ExchangeProp', DeletionProp]
  intro EP' L HL
  have HL' := (length_lt_iff_non_reduced).1 HL
  let j := max_reduced_word_index' HL'; use j
  let L1 := L.take j; let s := L.get j
  have Hj : L1.length = j := List.take_le_length L (le_of_lt j.2)
  have red_L1 : reduced_word L1 := reduced_take_max_reduced_word HL'
  have non_red_L1p : ¬reduced_word (L1 ++ [s]) := by
    rw [← List.take_get_lt L j.1 j.2]
    exact nonreduced_succ_take_max_reduced_word HL'
  have non_red_L1_s : ℓ((L1.gprod * s)) ≤ ℓ(L1.gprod) := by
    apply reduced_nonreduced_length_le red_L1 non_red_L1p
  let ⟨i, Hp⟩ := EP' red_L1 non_red_L1_s
  have Hlen : i < j.1 := by rw [← Hj]; exact i.2
  let i_fin_j : Fin j := ⟨i, Hlen⟩; use i_fin_j
  have h_L_decomp : (List.removeNth (List.removeNth L j) i) =
    (List.removeNth L1 i).gprod * (List.drop (j + 1) L) := by
    rw [← gprod_append]; apply congr_arg
    rw [← List.removeNth_append_lt, ← List.removeNth_eq_take_drop]
    exact i.2
  rw [h_L_decomp, ← Hp, ← gprod_singleton]
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
  by_cases hs : j.1 ≠ L.length ∧ i.1 ≠ L.length
  . exfalso
    have h_j_lt_k : j < L.length := by
      have h_j_le_k : j ≤ L.length := by
        apply Nat.le_of_lt_succ
        rw [Nat.succ_eq_add_one, ←List.length_append_singleton]
        exact j.2
      exact lt_of_le_of_ne h_j_le_k hs.left

    have h_i_lt_km1 : i < (L.removeNth j).length := by
      rw [List.length_removeNth];
      have := i.2
      have h_j_le_km1 : j ≤ L.length - 1 :=
        Nat.le_sub_one_of_lt h_j_lt_k
      linarith; assumption

    have : (L ++ [s]).gprod = ((L.removeNth j).removeNth i) ++ [s] := by
      calc
        (L ++ [s]).gprod = ((L ++ [s]).removeNth j).removeNth i := by exact h_dp
        _ = (L.removeNth j ++ [s]).removeNth i := by
          rw [List.removeNth_append_lt L [s] j.1 h_j_lt_k]
        _ = (L.removeNth j).removeNth i ++ [s] := by
          rw [List.removeNth_append_lt (L.removeNth j) [s] i'.1 h_i_lt_km1]

    have : L.gprod = (L.removeNth j).removeNth i := by
      rw [gprod_append_singleton, gprod_append_singleton] at this
      exact mul_right_cancel this

    have len_l_lt: ℓ(L) < List.length L := by
      rw [this]
      calc
        ℓ((L.removeNth j).removeNth i) ≤ ((L.removeNth j).removeNth i).length := by
          apply length_le_list_length
        _ = List.length L - 1 - 1 := by
          repeat rw [List.length_removeNth]
          repeat assumption
        _ < List.length L := Nat.sub_one_sub_lt_self <| Nat.pos_of_lt h_i_lt_k

    rw [length_eq_iff.1 red_L] at len_l_lt
    linarith

  . push_neg at hs
    by_cases h_s_eq_j : ↑j = List.length L
    . have : (L ++ [s]).gprod = (L.removeNth i) := by
        calc
          (L ++ [s]).gprod = (((L ++ [s]).removeNth j).removeNth i).gprod := by exact h_dp
          _ = (L.removeNth i') := by
            rw [List.append_remove_cancel_of_eq_last_index h_s_eq_j]
      let i'' : Fin L.length := ⟨i, h_i_lt_k⟩; use i''
      rw [←gprod_append_singleton, this]
    . exfalso; push_neg at h_s_eq_j
      let h_s_eq_i' := hs h_s_eq_j
      rw [h_s_eq_i'] at h_i_lt_k
      exact lt_irrefl _ h_i_lt_k

end OrderTwoGen

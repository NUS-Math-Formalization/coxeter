import Coxeter.OrderTwoGen
import Coxeter.Aux_

namespace OrderTwoGen
variable {G : Type*} [Group G] (S : Set G) [OrderTwoGen S]

local notation : max "ℓ(" g ")" => (length S g)

@[simp]
abbrev ExchangeProp  := ∀ {L : List S} {s : S}, reduced_word L →
  ℓ(s * L) ≤ ℓ(L) → ∃ (i: Fin L.length), (s : G) * L = L.removeNth i

@[simp]
abbrev ExchangeProp' := ∀ {L : List S} {s : S}, reduced_word L →
  ℓ(L * s) ≤ ℓ(L) → ∃ (i: Fin L.length), (L : G) * s = L.removeNth i

@[simp]
abbrev DeletionProp := ∀ (L:List S),
  ℓ( L ) < L.length →
  ∃ (j: Fin L.length), ∃ (i : Fin j), (L : G) = (L.removeNth j).removeNth i


lemma exchange_iff_exchange' : ExchangeProp S ↔ ExchangeProp' S:= by
  constructor
  · rw [ExchangeProp, ExchangeProp']
    intro EP L s h_red_L h_len
    have h_red_L_rev := reverse_is_reduced h_red_L
    have h_len_r :ℓ(s * L.reverse) ≤ ℓ(L.reverse) := by
      calc
      _ =  ℓ((s * L.reverse)⁻¹) := length_eq_inv_length
      _ =  ℓ(L * s) := by
        congr 1
        nth_rewrite 1 [gprod_reverse, inv_eq_self' s]
        group
      _ ≤  ℓ(L) := h_len
      _ =  ℓ(L.reverse) := by simp only [reverse_length_eq_length]
    let ⟨i, Hp⟩  := EP h_red_L_rev h_len_r
    rw [←gprod_cons] at Hp
    have h_i_lt_k : i < L.length := by have := i.2; simp only [List.length_reverse] at this; exact this
    let j := L.length - i - 1
    have h_j_lt_k : j < L.length := by apply Nat.sub_sub_one_lt_self; exact Nat.pos_of_lt h_i_lt_k
    let j' : Fin L.length := ⟨j, h_j_lt_k⟩
    use j'
    rw [←gprod_append_singleton]
    apply eq_of_one_div_eq_one_div
    rw [←inv_eq_one_div, ←inv_eq_one_div, ←OrderTwoGen.gprod_reverse, ←OrderTwoGen.gprod_reverse, List.reverse_cons'']
    rw [List.removeNth_reverse L i h_i_lt_k] at Hp
    rw [Hp];
  rw [ExchangeProp, ExchangeProp']
  intro EP' L s h_red_L h_len
  have h_red_L_rev := reverse_is_reduced h_red_L
  have h_len_r : ℓ(L.reverse * s) ≤ ℓ(L.reverse) := by
    calc
    _ = ℓ((L.reverse * s)⁻¹) := length_eq_inv_length
    _ = ℓ(s * L) := by
      congr 1
      nth_rewrite 1 [gprod_reverse, inv_eq_self' s]
      group
    _ ≤ ℓ(L) := h_len
    _ = ℓ(L.reverse) := by simp only [reverse_length_eq_length]
  let ⟨i, Hp⟩ := EP' h_red_L_rev h_len_r
  rw [←gprod_append_singleton] at Hp
  have h_i_lt_k : i < L.length := by have := i.2; simp only [List.length_reverse] at this; exact this
  let j := L.length - i - 1
  have h_j_lt_k : j < L.length := by apply Nat.sub_sub_one_lt_self; exact Nat.pos_of_lt h_i_lt_k
  let j' : Fin L.length := ⟨j, h_j_lt_k⟩
  use j'
  rw [←gprod_cons]
  apply eq_of_one_div_eq_one_div
  rw [←inv_eq_one_div, ←inv_eq_one_div, ←OrderTwoGen.gprod_reverse, ←OrderTwoGen.gprod_reverse, List.reverse_cons]
  rw [List.removeNth_reverse L i h_i_lt_k] at Hp
  rw [Hp]

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
    rw [←List.removeNth_append_lt, ←List.removeNth_eq_take_drop]
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

open OrderTwoGen

class CoxeterSystem {G : Type*} [Group G] (S : Set G) extends OrderTwoGen S where
  exchange : ExchangeProp S
  exchange' : ExchangeProp' S := (exchange_iff_exchange' S).1 exchange
  deletion : DeletionProp S := exchange_imp_deletion S exchange


section
class HOrderTwoGenGroup (G: Type*) extends Group G where
  S: Set G
  order_two :  ∀ (x:G) , x ∈ S →  x * x = (1 :G) ∧  x ≠ (1 :G)
  expression : ∀ (x:G) , ∃ (L : List S),  x = L.gprod

namespace HOrderTwoGenGroup
variable (G :Type*) [hG: HOrderTwoGenGroup G]
variable {H :Type*} [hH: HOrderTwoGenGroup H]

@[simp]
abbrev SimpleRefl := hG.S
@[simp,deprecated SimpleRefl]
abbrev SimpleRefls := hG.S



abbrev Refl (G:Type*) [HOrderTwoGenGroup G]: Set G:= {x:G| ∃ (w:G)(s : SimpleRefl G) , x = w*s*w⁻¹}

@[deprecated Refl]
abbrev Refls (G:Type*) [HOrderTwoGenGroup G]: Set G:= {x:G| ∃ (w:G)(s : SimpleRefl G) , x = w*s*w⁻¹}

instance SimpleRefls.toOrderTwoGen  : @OrderTwoGen H _ (SimpleRefl H) where
  order_two := hH.order_two
  expression := hH.expression


instance SimpleRefls.toOrderTwoGen'  : @OrderTwoGen H _ (hH.S) where
  order_two := hH.order_two
  expression := hH.expression

noncomputable def length  (g :H) := OrderTwoGen.length (hH.S) g

notation:65 "ℓ(" g:66 ")" => (length g)
variable (s w :G)
#check ℓ(s*w)
#check ℓ((s*w))
#check ℓ(s) - 1
end HOrderTwoGenGroup

class CoxeterGroup (G:Type*) extends HOrderTwoGenGroup G where
  exchange : OrderTwoGen.ExchangeProp S
  exchange': OrderTwoGen.ExchangeProp' S := (OrderTwoGen.exchange_iff_exchange' S).1 exchange
  deletion: OrderTwoGen.DeletionProp S := OrderTwoGen.exchange_imp_deletion S exchange

namespace CoxeterGroup
open HOrderTwoGenGroup

instance SimpleRefl_isCoxeterSystem  {G:Type*} [hG:CoxeterGroup G]: CoxeterSystem (SimpleRefl G) where
  exchange := hG.exchange
  exchange' := hG.exchange'
  deletion := hG.deletion

instance SimpleRefl_isCoxeterSystem'  {G:Type*} [hG:CoxeterGroup G]: CoxeterSystem (hG.S) where
  exchange := hG.exchange
  exchange' := hG.exchange'
  deletion := hG.deletion

instance {G:Type*} [hG:CoxeterGroup G]: HMul hG.S G G where
  hMul := fun s g => s.1 * g

instance {G:Type*} [hG:CoxeterGroup G]: HMul G hG.S G where
  hMul := fun g s => g * s.1

instance {G:Type*} [hG:CoxeterGroup G]: CoeOut hG.S G where
  coe := fun s => s.1


-- The length function defines a metric on the Coxeter group
noncomputable instance metric [CoxeterGroup G]: MetricSpace G := OrderTwoGen.metric <| SimpleRefl G

def leftAssocRefls (w : G) [CoxeterGroup G] := {t : G | t ∈ Refl G ∧ ℓ(((t:G)*w)) < ℓ(w)}

def rightAssocRefls (w : G) [CoxeterGroup G] := {t : G | t ∈ Refl G ∧ ℓ((w*(t:G))) < ℓ(w)}

def leftDescent (w : G) [hG:CoxeterGroup G] := leftAssocRefls w ∩ hG.S

def rightDescent (w : G) [hG:CoxeterGroup G] := rightAssocRefls w ∩ hG.S

section HeckeAux
variable {G : Type*} {w : G} [hG:CoxeterGroup G]

-- following lemmas assume G is CoxeterGroup, we can also have CoxeterMatrix version.
-- these lemmas are needed in Hecke.lean, because the def of Hecke use [CoxeterGroup G],
-- for convenience, the statements also use [CoxeterGroup G]
-- some lemmas are symmetric, such as muls_twice : w*s*s = w, the symm version is s*s*w = w.
-- this section only contain lemmas that needed in Hecke.lean, you can also formulate the symms if u want.
lemma leftDescent_NE_of_ne_one  (h : w ≠ 1) : Nonempty $ leftDescent w:= sorry

lemma rightDescent_NE_of_ne_one  (h : w ≠ 1) : Nonempty $ rightDescent w:= sorry

lemma ne_one_of_length_smul_lt {s : hG.S} {w:G} (lt: ℓ(s*w) < ℓ(w)) : w ≠ 1:= sorry

lemma length_smul_neq (s:hG.S) (w:G) : ℓ(s*w) ≠ ℓ(w) := sorry

lemma length_muls_neq (w:G) (t:hG.S) : ℓ(w*t) ≠ ℓ(w) := sorry

lemma length_diff_one {s:hG.S} {g : G} : ℓ(s*g) = ℓ(g) + 1  ∨ ℓ(g) = ℓ(s*g) + 1 :=sorry

lemma length_smul_of_length_lt {s : hG.S} {w:G} (h : w ≠ 1) (lt: ℓ(s*w) < ℓ(w)) : ℓ(s*w) = ℓ(w) - 1 := sorry

lemma length_muls_of_length_lt {s : hG.S} {w:G} (h : w ≠ 1) (lt: ℓ(w*s) < ℓ(w)) : ℓ(w*s) = ℓ(w) - 1 := sorry

lemma length_smul_of_length_gt {s : hG.S} {w:G} (gt: ℓ(w) < ℓ(s*w)) : ℓ(s*w) = ℓ(w) + 1 := sorry

lemma length_muls_of_length_gt {s : hG.S} {w:G} (gt: ℓ(w) < ℓ(w*s)) : ℓ(w*s) = ℓ(w) + 1 := sorry

lemma length_muls_of_mem_leftDescent  (h : w ≠ 1) (s : leftDescent w) : ℓ(s*w) = ℓ(w) - 1 :=sorry

lemma length_muls_of_mem_rightDescent  (h : w ≠ 1) (s : rightDescent w) : ℓ(w*s) = ℓ(w) - 1 :=sorry

lemma muls_twice (w:G) (s:hG.S) : w*s*s = w := sorry

lemma smul_eq_muls_of_length_eq (s t:hG.S) (w:G) :ℓ(s*w*t) = ℓ(w) ∧ ℓ(s*w)=ℓ(w*t) → s*w=w*t:= sorry

lemma length_smul_eq_length_muls_of_length_neq (s t :hG.S) (w:G): ℓ(s*w*t) ≠ ℓ(w) → ℓ(s*w)=ℓ(w*t):= sorry

-- ℓ(s*w*t) = ℓ(w) or ℓ(s*w*t) = ℓ(w) + 2 or ℓ(s*w*t) = ℓ(w) - 2
-- ℓ(s*w*t) < ℓ(w) →  ℓ(s*w*t) < ℓ(s*w) <ℓ(w) ∧ ℓ(s*w*t) < ℓ(w*t) <ℓ(w)
lemma length_lt_of_length_smuls_lt {s t:hG.S} {w:G} (h: ℓ(s*w*t) < ℓ(w)) : ℓ(s*w*t) < ℓ(s*w) := sorry

lemma length_lt_of_length_smuls_lt' {s t:hG.S} {w:G} (h: ℓ(s*w*t) < ℓ(w)) : ℓ(s*w) < ℓ(w) := sorry

lemma length_gt_of_length_smuls_gt {s t:hG.S} {w:G} (h: ℓ(w) < ℓ(s*w*t)) : ℓ(w) < ℓ(s*w) :=sorry

lemma length_gt_of_length_smuls_gt' {s t:hG.S} {w:G} (h: ℓ(w) < ℓ(s*w*t)) : ℓ(s*w) <ℓ(s*w*t) :=sorry

end HeckeAux


end CoxeterGroup

end



-- Palindrome words is moved here
section Palindrome
@[simp]
abbrev toPalindrome   (L : List β) : List β := L ++ L.reverse.tail

-- Note that 0-1 = 0
lemma toPalindrome_length {L : List β} : (toPalindrome L).length = 2 * L.length - 1 := by
  simp only [toPalindrome, List.length_append, List.length_reverse, List.length_tail]
  by_cases h: L.length=0
  . simp [h]
  . rw [<-Nat.add_sub_assoc]
    zify; ring_nf
    apply Nat.pos_of_ne_zero h

variable {G:Type*} [Group G] {S : Set G} [OrderTwoGen S]

local notation "T" => (OrderTwoGen.Refl S)

-- DLevel 2
lemma toPalindrome_in_Refl [OrderTwoGen S] {L:List S} (hL : L ≠ []) : (toPalindrome L:G) ∈ T := by
  sorry

-- Our index starts from 0
def toPalindrome_i  (L : List S) (i : ℕ) := toPalindrome (L.take (i+1))
local notation:210 "t(" L:211 "," i:212 ")" => toPalindrome_i L i

--def toPalindromeList (L : List S) : Set (List S):= List.image (toPalindrome_i L)'' Set.univ

--DLevel 3
lemma mul_Palindrome_i_cancel_i [OrderTwoGen S] {L : List S} (i : Fin L.length) : (t(L, i):G) * L = (L.removeNth i) := by sorry


-- DLevel 4
lemma distinct_toPalindrome_i_of  [OrderTwoGen S] {L : List S} :  reduced_word L → (∀ (i j : Fin L.length),  (hij : i ≠ j) → (toPalindrome_i L i) ≠ (toPalindrome_i L i)) := by
   sorry


lemma reduce_of_distinct_toPalindrome_i  [OrderTwoGen S] {L : List S} (hdel: DeletionProp S): ( ∀ i j:Fin L.length, (hij : i ≠ j) → (toPalindrome_i L i) ≠ (toPalindrome_i L i)) → reduced_word L := by sorry


end Palindrome


-- namespace CoxeterSystem

-- variable {G: Type*} [Group G] (S : Set G) [CoxeterSystem S]

-- end CoxeterSystem


-- structure expression where
-- element:G
-- reduced_expr:List S
-- reduced_property: reduced_word reduced_expr

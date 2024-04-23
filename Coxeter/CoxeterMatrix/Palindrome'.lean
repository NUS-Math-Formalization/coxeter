import Mathlib.Data.List.Basic
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Coxeter.Length

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs: CoxeterSystem M W)

open CoxeterMatrix List

local prefix:max "s" => cs.simple
local prefix:max "ℓ" => cs.length
local prefix:max "π" => cs.wordProd

namespace CoxeterSystem

protected def refl : Set W := {x : W | ∃ (w : W) (i : B), x = w * (s i) * w⁻¹}

end CoxeterSystem

local notation:max "T" => cs.refl

namespace List

def toPalindrome (L : List B) : List B := L ++ L.reverse.tail

/-- Note that 0-1 = 0 -/
lemma toPalindrome_length {L : List B} : (toPalindrome L).length = 2 * L.length - 1 := by
  simp only [toPalindrome, List.length_append, List.length_reverse, List.length_tail]
  by_cases h : L.length = 0
  . simp [h]
  . rw [← Nat.add_sub_assoc]
    zify; ring_nf
    apply Nat.pos_of_ne_zero h

/-- Our index starts from 0 -/
def toPalindrome_i (L : List S) (i : ℕ) := toPalindrome (L.take (i+1))

notation:210 "t(" L:211 "," i:212 ")" => toPalindrome_i L i

variable {L : List B}

lemma toPalindrome_in_Refl (hL : L ≠ []) : (π L.toPalindrome) ∈ T := by sorry
  /- apply OrderTwoGen.Refl.simplify.mpr
  use L.reverse.tail.reverse.gprod, (L.getLast hL)
  rw [← OrderTwoGen.gprod_reverse, List.reverse_reverse]
  have : L.reverse.tail.reverse.gprod * (L.getLast hL) = L.gprod := by
    have : L = L.reverse.tail.reverse ++ [L.getLast hL] :=
      (List.reverse_tail_reverse_append hL).symm
    nth_rw 3 [this]
    exact gprod_append_singleton.symm
  rw [this, toPalindrome, gprod_append] -/

lemma toPalindrome_i_in_Refl (i : Fin L.length) : (π (toPalindrome_i L i)) ∈ T := by sorry
  /- rw [toPalindrome_i]
  have tklen : (L.take (i+1)).length = i + 1 :=
    List.take_le_length L (by linarith [i.prop] : i + 1 ≤ L.length)
  have tkpos : (L.take (i+1)).length ≠ 0 := by linarith
  have h : List.take (i + 1) L ≠ [] := by
    contrapose! tkpos
    exact List.length_eq_zero.mpr tkpos
  exact toPalindrome_in_Refl h -/

lemma mul_Palindrome_i_cancel_i (i : Fin L.length) :
  (π (toPalindrome_i L i)) * (π L) = π (L.removeNth i) := by sorry
  /- rw [Palindrome.toPalindrome_i, toPalindrome, List.removeNth_eq_take_drop, List.take_get_lt _ _ i.2]
  simp only [gprod_append, gprod_singleton, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.tail]
  have : L = (L.take i).gprod * (L.drop i).gprod := by
    nth_rw 1 [← List.take_append_drop i L]
    rw [gprod_append]
  rw [this, mul_assoc, ← mul_assoc ((List.reverse (List.take i L)).gprod),
    OrderTwoGen.reverse_prod_prod_eq_one, one_mul, mul_assoc]
  apply (mul_right_inj (L.take i).gprod).2
  rw [← List.get_drop_eq_drop _ _ i.2, gprod_cons, ← mul_assoc]
  dsimp only [Fin.is_lt, Fin.eta, gt_iff_lt, List.getElem_eq_get _ _ i.2]
  rw [gen_square_eq_one', one_mul] -/

lemma distinct_toPalindrome_i_of_reduced (hr : cs.IsReduced L) (i j : Fin L.length) (hne : i ≠ j) : π (toPalindrome_i L i) ≠ π (toPalindrome_i L j) := by sorry
  /- intro rl
  by_contra! eqp
  rcases eqp with ⟨i, j, ⟨inej, eqp⟩⟩
  wlog iltj : i < j generalizing i j
  · have jlei : j ≤ i := le_of_not_lt iltj
    have ilej : i ≤ j := le_of_not_lt (this j i inej.symm eqp.symm)
    exact inej (le_antisymm ilej jlei)
  · have h : (toPalindrome_i L i).gprod * (toPalindrome_i L j) = 1 := by
      calc
        _ = (toPalindrome_i L i).gprod * (toPalindrome_i L i).gprod := by
          rw [← eqp]
        _ = 1 := by
          let ti : T := ⟨(t(L, i)).gprod, toPalindrome_i_in_Refl i⟩
          have : (ti : G) ^ 2 = 1 := OrderTwoGen.Refl.square_eq_one
          exact (pow_two _).subst (motive := fun (x : G) ↦ x = 1) this
    have lenremNjp : (L.removeNth j).length + 1 = L.length := List.removeNth_length L j
    have hi : i < (L.removeNth j).length := by
      rw [List.length_removeNth j.2]
      exact lt_of_lt_of_le iltj (Nat.le_pred_of_lt j.2)
    have hL : L.gprod = (L.removeNth j).removeNth i := by
      calc
        _ = (toPalindrome_i L i : G) * toPalindrome_i L j * L := by
          rw [h, one_mul]
        _ = (toPalindrome_i L i : G) * L.removeNth j := by
          rw [mul_assoc, removeNth_of_palindrome_prod]
        _ = (toPalindrome_i (L.removeNth j) i : G) * L.removeNth j := by
          repeat rw [toPalindrome_i]
          congr 3
          apply (List.take_of_removeNth L (Nat.add_one_le_iff.mpr iltj)).symm
        _ = (L.removeNth j).removeNth i :=
          removeNth_of_palindrome_prod (L.removeNth j) ⟨i.val, hi⟩
    have hlen : L.length ≤ ((L.removeNth j).removeNth i).length :=
      rl ((L.removeNth j).removeNth i) hL
    have lenremNip : ((L.removeNth j).removeNth i).length + 1 = (L.removeNth j).length :=
      List.removeNth_length (L.removeNth j) ⟨i.val, hi⟩
    linarith [hlen, lenremNip, lenremNjp] -/

end List

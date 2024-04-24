import Mathlib.Data.List.Basic
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Coxeter.Length
import Coxeter.Aux_

import Coxeter.OrderTwoGen

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs: CoxeterSystem M W)

open CoxeterMatrix List CoxeterSystem

local prefix:max "s" => cs.simple
local prefix:max "ℓ" => cs.length
local prefix:max "π" => cs.wordProd

section

-- The content here should be placed in another file, but for now, let's store them here temporarily.

namespace CoxeterSystem

protected def refl : Set W := {x : W | ∃ (w : W) (i : B), x = w * (s i) * w⁻¹}

end CoxeterSystem

end

local notation:max "T" => cs.refl

namespace List

@[pp_dot]
def toPalindrome (L : List B) : List B := L ++ L.reverse.tail

-- Note that 0-1 = 0.
lemma toPalindrome_length {L : List B} : (toPalindrome L).length = 2 * L.length - 1 := by
  simp only [toPalindrome, List.length_append, List.length_reverse, List.length_tail]
  by_cases h : L.length = 0
  . simp only [h, ge_iff_le, zero_le, tsub_eq_zero_of_le, add_zero, mul_zero]
  . rw [← Nat.add_sub_assoc]
    zify; ring_nf
    exact Nat.pos_of_ne_zero h

lemma nil_toPalindrome : ([] : List B).toPalindrome = [] := rfl

lemma toPalindrome_eq_nil_of_eq_nil (hL : L = []) : L.toPalindrome = [] := by
  rw [hL]
  rfl

-- Our index starts from 0.
def toPalindrome_i (L : List S) (i : ℕ) := toPalindrome (L.take (i + 1))

--notation:210 "t(" L:211 "," i:212 ")" => toPalindrome_i L i

variable {L : List B}

@[simp]
lemma toPalindrome_rev : L.toPalindrome.reverse = L.toPalindrome := by
  by_cases hL : L = []
  · rw [hL]
    sorry
  · unfold toPalindrome
    simp only [reverse_append]
    sorry

@[simp]
lemma toPalindrome_inv_eq_self : (π L.toPalindrome)⁻¹ = π L.toPalindrome := sorry

@[simp]
lemma toPalindrome_i_rev (i : ℕ) : (toPalindrome_i L i).reverse = toPalindrome_i L i :=
  (L.take (i + 1)).toPalindrome_rev

lemma toPalindrome_in_refl (hL : L ≠ []) : π L.toPalindrome ∈ T := by
  use π L.reverse.tail.reverse, (L.getLast hL)
  rw [← wordProd_reverse, reverse_reverse, ← wordProd_concat,
    ← wordProd_append, toPalindrome, concat_eq_append]
  congr
  exact (reverse_tail_reverse_append hL).symm

lemma toPalindrome_i_eq_take_mul_take_inv {i : ℕ} (hi : i < L.length) : π (toPalindrome_i L i) = π (L.take (i + 1)) * (π (L.take i))⁻¹ := by
  rw [← wordProd_reverse, ← wordProd_append, toPalindrome_i, toPalindrome]
  have h : L.take i = (L.take (i + 1)).reverse.tail.reverse := by
    rw [← (L.take (i + 1)).dropLast_eq_reverse_tail_reverse]
    by_cases hi : i + 1 < L.length
    · rw [dropLast_take hi, Nat.pred_succ]
    · have hi : i + 1 = L.length := by linarith
      rw [hi, take_length, dropLast_eq_take, ← hi, Nat.pred_succ]
  rw [h, reverse_reverse]

lemma toPalindrome_i_eq_take_mul_take_inv' {i : ℕ} (hi : i < L.length) : π (toPalindrome_i L i) = π (L.take i) * (π (L.take (i + 1)))⁻¹ := sorry

lemma toPalindrome_i_in_refl (hL : L ≠ []) {i : ℕ} : π (toPalindrome_i L i) ∈ T :=
  toPalindrome_in_refl cs <| (L.take_eq_nil_iff).not.mpr <| by
    simp only [hL, add_eq_zero, one_ne_zero, and_false, or_self, not_false_eq_true]

lemma toPalindrome_i_mul_eq_removeNth {i : ℕ} (hi : i < L.length) : (π (toPalindrome_i L i)) * (π L) = π (L.removeNth i) := by
  have h : π L = π (L.take (i + 1)) * π (L.drop (i + 1)) := by
    rw [← wordProd_append, take_append_drop (i + 1) L]
  rw [h, removeNth_eq_take_drop, wordProd_append, ← mul_assoc]
  rw [L.toPalindrome_i_eq_take_mul_take_inv' cs hi, inv_mul_cancel_right]

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

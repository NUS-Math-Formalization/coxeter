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

@[simp]
lemma nil_toPalindrome : ([] : List B).toPalindrome = [] := rfl

lemma toPalindrome_eq_nil_of_eq_nil (hL : L = []) : L.toPalindrome = [] := by
  rw [hL]
  rfl

-- Our index starts from 0.
def toPalindrome_i (L : List S) (i : ℕ) := toPalindrome (L.take (i + 1))

-- notation:210 "t(" L:211 "," i:212 ")" => toPalindrome_i L i

variable {L : List B}

@[simp]
lemma toPalindrome_rev : L.toPalindrome.reverse = L.toPalindrome := by
  by_cases hL : L = []
  · rw [hL]
    rfl
  · rw [toPalindrome, reverse_append]
    nth_rw 3 [← reverse_tail_reverse_append hL]
    rw [append_assoc, singleton_append, append_cancel_left_eq, reverse_head]
    congr

@[simp]
lemma toPalindrome_inv_eq_self : (π L.toPalindrome)⁻¹ = π L.toPalindrome := by
  rw [← wordProd_reverse, toPalindrome_rev]

@[simp]
lemma toPalindrome_sq_eq_one : π L.toPalindrome * π L.toPalindrome = 1 := by
  nth_rw 1 [← L.toPalindrome_inv_eq_self, inv_mul_self]

@[simp]
lemma toPalindrome_i_rev (i : ℕ) : (toPalindrome_i L i).reverse = toPalindrome_i L i :=
  (L.take (i + 1)).toPalindrome_rev

@[simp]
lemma toPalindrome_i_inv_eq_self (i : ℕ) : (π (toPalindrome_i L i))⁻¹ = π (toPalindrome_i L i) :=
  (L.take (i + 1)).toPalindrome_inv_eq_self cs

@[simp]
lemma toPalindrome_i_sq_eq_one (i : ℕ) : π (toPalindrome_i L i) * π (toPalindrome_i L i) = 1 :=
  (L.take (i + 1)).toPalindrome_sq_eq_one cs

lemma toPalindrome_in_refl (hL : L ≠ []) : π L.toPalindrome ∈ T := by
  use π L.reverse.tail.reverse, (L.getLast hL)
  rw [← wordProd_reverse, reverse_reverse, ← wordProd_concat]
  rw [← CoxeterSystem.wordProd_append, toPalindrome, concat_eq_append]
  congr
  exact (reverse_tail_reverse_append hL).symm

lemma toPalindrome_i_eq_take_mul_take_inv {i : ℕ} (hi : i < L.length) : π (toPalindrome_i L i) = π (L.take (i + 1)) * (π (L.take i))⁻¹ := by
  rw [← wordProd_reverse, ← CoxeterSystem.wordProd_append, toPalindrome_i, toPalindrome]
  have h : L.take i = (L.take (i + 1)).reverse.tail.reverse := by
    rw [← (L.take (i + 1)).dropLast_eq_reverse_tail_reverse]
    by_cases hi : i + 1 < L.length
    · rw [dropLast_take hi, Nat.pred_succ]
    · have hi : i + 1 = L.length := by linarith
      rw [hi, take_length, dropLast_eq_take, ← hi, Nat.pred_succ]
  rw [h, reverse_reverse]

lemma toPalindrome_i_eq_take_mul_take_inv' {i : ℕ} (hi : i < L.length) : π (toPalindrome_i L i) = π (L.take i) * (π (L.take (i + 1)))⁻¹ := by
  rw [← toPalindrome_i_rev, wordProd_reverse, toPalindrome_i_eq_take_mul_take_inv cs hi]
  simp only [mul_inv_rev, mul_assoc, inv_inv]

lemma toPalindrome_i_in_refl (hL : L ≠ []) {i : ℕ} : π (toPalindrome_i L i) ∈ T :=
  toPalindrome_in_refl cs <| (L.take_eq_nil_iff).not.mpr <| by
    simp only [hL, add_eq_zero, one_ne_zero, and_false, or_self, not_false_eq_true]

lemma toPalindrome_i_mul_eq_removeNth {i : ℕ} (hi : i < L.length) : (π (toPalindrome_i L i)) * (π L) = π (L.removeNth i) := by
  have h : π L = π (L.take (i + 1)) * π (L.drop (i + 1)) := by
    rw [← CoxeterSystem.wordProd_append, take_append_drop (i + 1) L]
  rw [h, removeNth_eq_take_drop, CoxeterSystem.wordProd_append, ← mul_assoc]
  rw [L.toPalindrome_i_eq_take_mul_take_inv' cs hi, inv_mul_cancel_right]

lemma distinct_toPalindrome_i_of_reduced (hr : cs.IsReduced L) {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (hij : i ≠ j) : π (toPalindrome_i L i) ≠ π (toPalindrome_i L j) := by
  intro heq
  wlog iltj : i < j generalizing i j
  · exact hij (Nat.le_antisymm (le_of_not_lt (this hj hi hij.symm heq.symm)) (le_of_not_lt iltj))
  · have hij : i < length (removeNth L j) :=
      (iltj.trans_le (Nat.le_sub_one_of_lt hj)).trans_eq (L.length_removeNth hj).symm
    have hL : π L = π ((L.removeNth j).removeNth i) := by
      calc
        _ = π (toPalindrome_i L i) * π (toPalindrome_i L j) * π L := by
          rw [heq, L.toPalindrome_i_sq_eq_one cs j, one_mul]
        _ = π (toPalindrome_i L i) * π (L.removeNth j) := by
          rw [mul_assoc, toPalindrome_i_mul_eq_removeNth cs hj]
        _ = π (toPalindrome_i (L.removeNth j) i) * π (L.removeNth j) := by
          simp only [toPalindrome_i, mul_left_inj]
          congr 2
          exact (L.take_of_removeNth (Nat.add_one_le_iff.mpr iltj)).symm
        _ = π ((L.removeNth j).removeNth i) :=
          (L.removeNth j).toPalindrome_i_mul_eq_removeNth cs hij
    have h := length_wordProd_le cs ((L.removeNth j).removeNth i)
    rw [← hL] at h
    have hle := hr.symm.trans_le h
    have hm := (L.removeNth j).length_removeNth hij
    rw [L.length_removeNth hj] at hm
    omega

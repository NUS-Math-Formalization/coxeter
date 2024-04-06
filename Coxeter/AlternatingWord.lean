import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Parity

import Coxeter.Aux_

namespace AlternatingWord

def alternating_word (s t : α) (n : ℕ) : List α :=
  match n with
  | 0 => []
  | m + 1 => s :: alternating_word t s m

lemma alternating_word_range (s t : α) (n : ℕ) : alternating_word s t n = (List.range n).map (fun x ↦ if x % 2 = 0 then s else t) := by
  induction' n with m ih generalizing s t
  · simp only [Nat.zero_eq, List.range_zero, List.map_nil, alternating_word]
  · rw [alternating_word, ih t s, List.range_eq_range', List.range_eq_range',
      ← List.range'_append_1 0 1 m, List.map_append, List.range'_eq_map_range 1 m, List.range_eq_range']
    simp only [List.range'_one, List.map_cons, Nat.zero_mod, reduceIte, List.map_nil, List.map_map,
      List.singleton_append, List.cons.injEq, true_and]
    congr
    ext x
    dsimp only [Function.comp_apply]
    have : (if ¬¬(1 + x) % 2 = 0 then s else t) = if x % 2 = 0 then t else s := by
      rw [ite_not]
      congr
      simp only [Nat.mod_two_ne_zero, eq_iff_iff]
      rw [add_comm, ← Nat.succ_eq_add_one]
      exact Nat.succ_mod_two_eq_one_iff
    rw [← this]
    congr
    rw [not_not]

lemma alternating_word_nil (s t : α) : alternating_word s t 0 = [] := by
  rw [alternating_word]

lemma alternating_word_singleton (s t : α) : alternating_word s t 1 = [s] := by
  rw [alternating_word, alternating_word_nil]

lemma alternating_word_length (s t : α) (n : ℕ) : (alternating_word s t n).length = n := by
  induction' n with m ih generalizing s t
  rw [alternating_word_nil, List.length_nil]
  rw [alternating_word, List.length_cons, ih t s]

lemma alternating_word_take (s t : α) (n i : ℕ) (h : i ≤ n) :
    (alternating_word s t n).take i = alternating_word s t i := by
  rw [alternating_word_range, alternating_word_range, ← List.map_take, List.take_range h]

-- DLevel 2
lemma alternating_word_append_odd (s t : α) (n m : ℕ) (h1 : m ≤ n) (h2 : Odd m) :
    alternating_word s t n = alternating_word s t m ++ alternating_word t s (n - m) := by
  nth_rw 1 [← Nat.sub_add_cancel (h1)]
  set d := n - m
  rcases h2 with ⟨k, ek⟩
  rw [ek]
  clear ek
  induction k with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add, Nat.add_one, Nat.succ_eq_add_one]
    rw [alternating_word_singleton, alternating_word, List.singleton_append]
  | succ y ih =>
    rw [Nat.add_one, Nat.succ_eq_add_one, Nat.succ_eq_add_one, mul_add]
    nth_rw 2 [two_mul]
    nth_rw 3 [two_mul]
    repeat rw [← add_assoc]
    rw [alternating_word, alternating_word]
    rw [add_assoc, ih]
    rw [alternating_word, alternating_word]
    repeat rw [← List.cons_append]

-- DLevel 2
lemma alternating_word_append_even (s t : α) (n m : ℕ) (h1 : m ≤ n) (h2 : Even m) :
    alternating_word s t n = alternating_word s t m ++ alternating_word s t (n - m) := by
  nth_rw 1 [← Nat.sub_add_cancel (h1)]
  set d := n - m
  rcases h2 with ⟨k, ek⟩
  rw [ek, ← two_mul]
  clear ek
  induction k with
  | zero =>
    rw [Nat.mul_zero, Nat.add_zero, alternating_word_nil, List.nil_append]
  | succ y ih =>
    rw [Nat.succ_eq_add_one, mul_add, two_mul, two_mul, ← add_assoc]
    repeat rw [alternating_word]
    rw [← two_mul, ih]
    repeat rw [← List.cons_append]

lemma odd_alternating_word_reverse (s t : α) (i : ℕ) (h : Odd i) :
  (alternating_word s t i).reverse = alternating_word s t i := by
  rcases h with ⟨k, ek⟩
  rw [ek]
  clear ek
  induction' k with l ih
  . simp only [Nat.zero_eq, mul_zero, zero_add]
    rfl
  . rw [Nat.succ_eq_add_one, mul_add, mul_one, add_assoc, add_comm 2 1, ← add_assoc]
    nth_rw 1 [alternating_word_append_odd s t (2 * l + 1 + 2) (2 * l + 1) (by simp) (by simp)]
    rw [alternating_word_append_even s t (2 * l + 1 + 2) 2 (by simp) (by simp)]
    simp only [add_tsub_cancel_left, List.reverse_append, add_tsub_cancel_right,
      ih, List.append_cancel_right_eq]
    rfl

lemma even_alternating_word_reverse (s t : α) (i : ℕ) (h : Even i) :
  (alternating_word s t i).reverse = alternating_word t s i := by
  rcases h with ⟨k, ek⟩
  rw [← two_mul] at ek
  rw [ek]
  clear ek
  induction' k with l ih
  . simp only [Nat.zero_eq, mul_zero]
    rfl
  . rw [Nat.succ_eq_add_one, mul_add, mul_one,
      alternating_word_append_even s t (2 * l + 2) 2 (by simp) (by simp),
      alternating_word_append_even t s (2 * l + 2) (2 * l) (by simp) (by simp),
      List.reverse_append, add_tsub_cancel_right, add_tsub_cancel_left, ih]
    rfl

lemma alternating_word_map (s t : α) (f : α → A) (n : ℕ) :
  (alternating_word s t n).map f = alternating_word (f s) (f t) n := by
  induction' n with k ih generalizing s t
  . simp only [Nat.zero_eq]
    rfl
  . rw [alternating_word, alternating_word, List.map_cons]
    simp only [List.cons.injEq, true_and]
    exact ih t s

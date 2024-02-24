import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.List.Range
import Mathlib.Algebra.Module.Equiv
import Mathlib.Data.List.Palindrome


#check List.eraseDups
#check List.eraseReps
#check List.groupBy

namespace  List
variable {α : Type _} [BEq α] [Inhabited α]

lemma append_singleton_ne_nil (L : List α) (a : α) : L ++ [a] ≠ [] := by {
  induction L with
  | nil => {simp}
  | cons hd tail _ => {simp}
}

lemma length_hd_tail_eq_succ_length (L : List α) (a : α) : (a :: L).length = L.length + 1 := by simp


lemma append_remove_cancel_of_eq_last_index {a : α} {n : ℕ} (h : n = L.length) :
  (L ++ [a]).removeNth n = L := by
  induction L generalizing n with
  | nil => simp at h; simp [h]
  | cons hd tail ih => simp at h; simp [h, ih]


lemma length_append_singleton (L : List α) (a : α) : (L ++ [a]).length = L.length + 1 := by
  induction L with
  | nil => simp
  | cons _ tail _ => simp

#check length_removeNth


lemma take_le_length (L : List α) (h : n ≤ L.length)  : (L.take n).length = n := by
  simp only [length_take,ge_iff_le, h, min_eq_left]

lemma removeNth_eq_take_drop {α : Type _} (L: List α) (n : ℕ) : L.removeNth n = L.take n ++ L.drop (n+1) := by
  revert n
  induction L with
  | nil => {intro n; simp only [removeNth, take_nil, drop, append_nil]}
  | cons hd tail ih =>
      intro n
      match n with
      | 0 => {simp only [removeNth, take, drop, nil_append]}
      | k+1 =>
        simp only [removeNth, Nat.add_eq, add_zero, take, drop, cons_append, cons.injEq, true_and]
        exact ih k

@[deprecated removeNth_eq_take_drop]
lemma remove_nth_eq_take_drop {α : Type _} (L: List α) (n : ℕ) : L.removeNth n = L.take n ++ L.drop (n+1) := by
  revert n
  induction L with
  | nil => {intro n; simp only [removeNth, take_nil, drop, append_nil]}
  | cons hd tail ih =>
      intro n
      match n with
      | 0 => {simp only [removeNth, take, drop, nil_append]}
      | k+1 =>
        simp only [removeNth, Nat.add_eq, add_zero, take, drop, cons_append, cons.injEq, true_and]
        exact ih k

lemma removeNth_length {α : Type _} (L: List α) (n : Fin L.length) : (L.removeNth n).length + 1 = L.length := by
  revert n
  induction L with
  | nil =>
    intro n
    rw [length] at n
    rcases n with ⟨v, h⟩
    by_contra
    exact (not_le.mpr h) (Nat.zero_le v)
  | cons hd tail ih =>
    intro n
    match n.val, n.prop with
    | 0, _ => rw [removeNth, length]
    | m + 1, nprop =>
      rw [length] at nprop
      rw [removeNth, length, length]
      rw [ih ⟨m, (add_lt_add_iff_right 1).mp nprop⟩]

lemma sub_one_lt_self (n: ℕ) (_ : 0 < n) : n - 1 < n := match n with
| 0 => by {contradiction}
| n+1 => by {simp}


lemma take_drop_get {α : Type _} (L: List α) (n : ℕ) (h : n < L.length):
  L = L.take n ++ [L.get ⟨n,h⟩] ++ L.drop (n+1) := by
  have Hn :=  List.take_append_drop n L
  have Hd := List.drop_eq_get_cons h
  rw [Hd] at Hn
  simp only [append_assoc, singleton_append, Hn]

@[simp]
lemma drop_take_nil {α : Type _} {L : List α} {n : ℕ} : (L.take n).drop n = [] := by
  have h := drop_take n 0 L
  simp only [add_zero, take] at h
  exact h


-- DLevel 2
lemma take_get_lt {α : Type _} (L: List α) (n : ℕ) (h : n < L.length) :
  L.take (n+1) = L.take n ++ [L.get ⟨n, h⟩] := by
  have h1 : L = L.take n ++ [L.get ⟨n, h⟩] ++ L.drop (n+1) := take_drop_get L n h
  have h2 : L = L.take (n+1) ++ L.drop (n+1) := symm (take_append_drop (n+1) L)
  nth_rw 1 [h2] at h1
  exact (append_left_inj (drop (n+1) L)).mp h1


lemma get_eq_nthLe {α : Type _} {L: List α} {n : ℕ} {h : n < L.length} :
  L.get ⟨n, h⟩ = L.nthLe n h := by rfl


/-

lemma take_drop_nth_le {α : Type _} (L: List α) (n : ℕ) (h : n < L.length): L = L.take n ++ [L.nthLe n h] ++ L.drop (n+1) := by {
  have := take_drop_get L n h
  rw [List.nthLe_eq]
  exact this
}
-/
@[simp]
lemma removeNth_append_lt {α : Type _} (L1 L2: List α) (n : ℕ) (h : n < L1.length) :
  (L1 ++ L2).removeNth n = L1.removeNth n ++ L2 := by
  rw [removeNth_eq_take_drop, removeNth_eq_take_drop]
  rw [List.take_append_of_le_length (le_of_lt h)]
  have : (L1 ++ L2).drop (n + 1) = L1.drop (n + 1) ++ L2 :=
    drop_append_of_le_length (by linarith)
  rw [this, append_assoc]

-- lemma removeNth_append_ge {α : Type _} (L1 L2: List α) (n : ℕ) (h : n ≥ L1.length) :
--   (L1 ++ L2).removeNth n = L1 ++ L2.removeNth (n - L1.length) := by
--   rw [removeNth_eq_take_drop, removeNth_eq_take_drop]
--   rw [List.take_append_of_le_length (le_of_ge h)]



lemma removeNth_reverse (L : List α) (n : ℕ) (h : n < L.length) :
  (L.reverse).removeNth n = (L.removeNth (L.length - n - 1)).reverse := by
  rw [removeNth_eq_take_drop, removeNth_eq_take_drop]
  rw [List.reverse_append, List.reverse_take n (Nat.le_of_lt h), Nat.sub_sub]
  nth_rw 6 [←List.reverse_reverse L]; nth_rw 7 [←List.reverse_reverse L]
  rw [List.length_reverse L.reverse]
  rw [List.reverse_take (length (reverse L) - (n + 1)) (Nat.sub_le L.reverse.length (n+1)),
    List.reverse_reverse, List.length_reverse]
  rw [←Nat.sub_sub L.length n 1, Nat.sub_add_cancel (by
    apply Nat.le_of_add_le_add_right; swap; exact n;
    rw [Nat.sub_add_cancel]; rw [Nat.add_comm]; exact Nat.succ_le_of_lt h;
    exact Nat.le_of_lt h), Nat.sub_sub]
  have : length L - (length L - (n + 1)) = n + 1 := by
    apply Nat.add_right_cancel
    swap; exact (length L - (n + 1))
    rw [Nat.sub_add_cancel, Nat.add_sub_of_le]
    . linarith
    exact Nat.sub_le L.length (n+1);
  rw [this];

lemma reverse_cons'' (L : List α) (a : α) : (L ++ [a]).reverse = a :: L.reverse := by
  rw [List.reverse_append, List.reverse_singleton]; simp;

lemma eq_iff_reverse_eq (L1 L2 : List α) : L1.reverse = L2.reverse ↔ L1 = L2 := by
  constructor
  . intro h; rw [←List.reverse_reverse L1, ←List.reverse_reverse L2, h, List.reverse_reverse]
  . intro h; rw [h]

#check reverse_append

#check dropLast_concat

/-
lemma removeNth_length_sub_one (L:List α) : removeNth L (L.length - 1) = dropLast L :=by sorry

lemma removeNth_concat {a:α} (L:List α) : removeNth (concat L a) L.length = L:=by sorry
-/

end List


namespace Nat

lemma pos_of_lt {i n: Nat} (h : i < n) : 0 < n := by
  calc
  0 ≤ i := zero_le _
  _ < _ := h

lemma sub_one_sub_lt_self {i n: Nat} (h : 0 < n) : n - 1 - i < n := by
  calc
  _ ≤ n-1 := by simp
  _ < _ := Nat.pred_lt <| pos_iff_ne_zero.1 h

lemma sub_sub_one_lt_self {i n: Nat} (h : 0 < n) : n - i - 1 < n := by
  rw [Nat.sub_sub, Nat.add_comm, ←Nat.sub_sub]
  exact sub_one_sub_lt_self h

end Nat

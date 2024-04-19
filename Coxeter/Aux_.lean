import Std.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.List.Range
import Mathlib.Algebra.Module.Equiv
--import Mathlib.Data.List.Palindrome
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Logic.Equiv.Fin


import Coxeter.AttrRegister

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
  | nil => rw [h]; simp
  | cons hd tail ih => rw [h]; simp [ih]

lemma length_append_singleton (L : List α) (a : α) : (L ++ [a]).length = L.length + 1 := by
  induction L with
  | nil => simp
  | cons _ tail _ => simp

lemma take_le_length (L : List α) (h : n ≤ L.length)  : (L.take n).length = n := by
  simp only [length_take,ge_iff_le, h, min_eq_left]

lemma takeFront {α : Type _} (s : α) (L : List α) (i : Fin L.length) :
  (L ++ [s] ++ L.reverse).take i.1 = L.take i.1 := by
  rw [List.append_assoc, List.take_append_of_le_length]
  exact Nat.le_of_lt i.2

lemma takeBehind {α : Type _} (s : α) (L : List α) (i : Fin L.length) :
  (L ++ [s] ++ L.reverse).take (2 * L.length - i.1) = L ++ [s] ++ L.reverse.take (L.length - 1 - i.1) := by
  rw [two_mul, Nat.add_sub_assoc (by exact le_of_lt i.2)]
  rw [List.append_assoc]
  rw [List.take_append]
  have : List.length L - i = 1 + List.length L - 1 - i := by
    rw [Nat.add_comm, Nat.add_one_sub_one]
  rw [this]
  nth_rw 1 [←List.length_singleton s]
  rw [Nat.add_sub_assoc (by exact Nat.one_le_of_lt (i.2)), Nat.add_sub_assoc (by exact Nat.le_sub_one_of_lt i.2)]
  rw [List.take_append, List.append_assoc]

lemma reverse_take_eq_drop_reverse {α : Type _} (L : List α) (i : Fin L.length)
  : (L.reverse.take (List.length L - 1 - i.1)) = (L.drop (1 + i.1)).reverse := by
  rw [Nat.sub_sub, List.reverse_take _ (Nat.sub_le (List.length L) (1 + i.1))]
  congr
  have : 1 + i.1 ≤ L.length := by rw [add_comm]; exact i.2
  rw [Nat.sub_sub_self this]


/-map and removeNth are commute with each other-/
lemma map_removeNth_comm {α : Type*} {β : Type*} {f : α → β } (L : List α) (i : ℕ)
: (L.removeNth i).map f = (L.map f).removeNth i := by
  induction' L with x xa h generalizing i
  . simp only [removeNth, map_nil]
  . induction' i with n _
    . simp only [removeNth]
    . simp_rw [removeNth,map_cons, h n]

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

lemma append_singleton_reverse_length {α : Type _} (s : α) (L : List α) :
  (L ++ [s] ++ L.reverse).length = 2 * L.length + 1 := by
  rw [List.length_append, List.length_append, List.length_reverse, List.length_singleton,
    add_comm, ← add_assoc, ← two_mul]

lemma lt_append {α : Type _} (s : α) (L : List α) : L.length < (L ++ [s]).length := by
  rw [List.length_append, List.length_singleton]
  exact Nat.le.refl

lemma lt_append' {α : Type _} (s : α) (L : List α) (x : Fin L.length) : x.1 < (L ++ [s]).length := by
  rw [List.length_append, List.length_singleton]
  exact Fin.val_lt_of_le x (Nat.le.step Nat.le.refl)

lemma lt_append_singleton_reverse {α : Type _} (s : α) (L : List α) (x : Fin L.length) :
  x.1 < (L ++ [s] ++ L.reverse).length := by
  rw [List.length_append, List.length_append]
  linarith [x.2]

lemma lt_append_singleton_reverse' {α : Type _} (s : α) (L : List α) (x : Fin L.length) :
  2 * L.length - x.1 < (L ++ [s] ++ L.reverse).length := by
  rw [List.length_append, List.length_append, List.length_singleton,
    List.length_reverse, two_mul, Nat.add_sub_assoc (by linarith [x.2]), add_assoc]
  refine Nat.add_lt_add_left ?_ L.length
  rw [add_comm]
  exact Nat.lt_succ.mpr (Nat.sub_le L.length x)

lemma not_lt_append_singleton {α : Type _} (s : α) (L : List α) (x : Fin L.length) :
  ¬2 * L.length - x.1 < (L ++ [s]).length := by
  push_neg
  rw [two_mul, List.length_append, List.length_singleton,
    Nat.add_sub_assoc (by linarith [x.2])]
  refine Nat.add_le_add_left (Nat.le_sub_of_add_le ?_) L.length
  rw [add_comm]
  exact x.2

lemma lt_append_singleton' {α : Type _} (s : α) (L : List α) (x : Fin L.length) :
  2 * L.length - x.1 - (L ++ [s]).length < L.reverse.length := by
  have : 2 * L.length - x.1 < (L ++ [s] ++ L.reverse).length := lt_append_singleton_reverse' s L x
  rw [List.length_append] at this
  apply Nat.sub_lt_left_of_lt_add
  apply Nat.le_of_not_lt (not_lt_append_singleton s L x)
  rw [← List.length_append]
  apply lt_append_singleton_reverse'

lemma lt_reverse_reverse {α : Type _} (s : α) (L : List α) (x : Fin L.length) :
  L.reverse.length - 1 - (2 * L.length - x.1 - (L ++ [s]).length) < L.reverse.reverse.length := by
  repeat rw [List.length_reverse]
  refine lt_of_le_of_lt (Nat.sub_le _ _) ?_
  exact Nat.sub_lt_of_pos_le (by norm_num) (by linarith [x.2])

lemma reverse_reverse_get {α : Type _} (s : α) (L : List α) (x : Fin L.length) :
  L.reverse.reverse.get ⟨L.reverse.length - 1 - (2 * L.length - x.1 - (L ++ [s]).length),
    (lt_reverse_reverse s L x)⟩ = L.get x := by
  simp only [List.length_reverse, List.length_append, List.length_singleton,
    two_mul, Nat.sub_sub, Nat.add_comm x (L.length + 1), List.reverse_reverse]
  have : L.length - (1 + (L.length + L.length - (L.length + 1 + x.1))) = x := by
    nth_rw 2 [← Nat.sub_sub]
    nth_rw 2 [← Nat.sub_sub]
    rw [Nat.add_sub_cancel, Nat.sub_sub, ← Nat.add_sub_assoc (by linarith [x.2]),
      add_comm 1 L.length, ← Nat.sub_sub, Nat.add_sub_cancel]
    exact Nat.sub_sub_self (by linarith [x.2])
  simp only [this]
  have : x.1 < L.reverse.reverse.length := by
    rw [List.reverse_reverse]
    exact x.2
  congr 1
  · exact List.reverse_reverse L
  · exact (Fin.heq_ext_iff (by rw [List.reverse_reverse L])).mpr rfl

lemma reverse_drop {α : Type _} (L : List α) (n : ℕ) :
  (L.drop n).reverse = L.reverse.take (L.length - n) := by
  induction L generalizing n with
  | nil => simp only [drop_nil, reverse_nil, take_nil]
  | cons hd tail ih =>
    induction n with
    | zero =>
      simp only [Nat.zero_eq, drop_zero, reverse_cons, tsub_zero]
      rw [← length_reverse, reverse_cons, take_length]
    | succ n =>
      simp only [drop_succ_cons, length_cons, Nat.succ_sub_succ_eq_sub, reverse_cons]
      rw [ih n, take_append_of_le_length]
      rw [length_reverse]
      exact Nat.sub_le (length tail) n

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
  have h := drop_take n n L
  simp at h
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

lemma remove_after_L_length (L : List α) {i : ℕ} (h : L.length ≤ i)
  : L.removeNth i = L := by
  have remove_after_L_length': L.removeNth ((i - L.length) + L.length) = L := by
    set j := i - L.length
    induction' j with k ih
    . simp only [Nat.zero_eq, zero_add]
      induction L with
      | nil => simp only [removeNth]
      | cons hd tail ih =>
        simp only [removeNth, Nat.add_eq, add_zero, cons.injEq, true_and]
        apply ih
        exact Nat.lt_succ.1 (Nat.le.step h)
    . induction L with
      | nil => simp only [removeNth]
      | cons hd tail ih' =>
        set L := hd :: tail
        simp only [removeNth, Nat.add_eq, add_zero, cons.injEq, true_and,L]
        apply ih'
        exact Nat.lt_succ.1 (Nat.le.step h)
        simp only [removeNth, Nat.add_eq, add_zero, cons.injEq, true_and,L] at ih
        apply ih
  nth_rw 2 [← remove_after_L_length']
  rw [Nat.sub_add_cancel h]

lemma removeNth_cons (s : α) (L : List α) {i : ℕ} (h : i > 0) :
  (s :: L).removeNth i = s :: L.removeNth (i - 1) := by
  have : i = i - 1 + 1 := by exact (Nat.sub_eq_iff_eq_add h).mp rfl
  nth_rw 1 [this]
  induction' (i - 1) with k _
  . simp only [removeNth, Nat.zero_eq]
  . simp only [removeNth]

-- DLevel 2
lemma take_of_removeNth (L : List α) {i j : ℕ} (h : i ≤ j) :
    (L.removeNth j).take i = L.take i := by
  by_cases h' : j ≥ L.length
  . have : L.removeNth j = L := remove_after_L_length L h'
    rw [this]
  . rw [removeNth_eq_take_drop]
    push_neg at h'
    have h'' : j ≤ L.length := by linarith
    have : (L.take j).length = j := take_le_length L h''
    have i_le_j' : i ≤ (L.take j).length := by linarith
    have : L.take i = (L.take j).take i := by
      nth_rw 1 [← min_eq_left h]
      apply Eq.symm
      apply List.take_take i j L
    rw [this]
    exact take_append_of_le_length i_le_j'


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

lemma reverseList_nonEmpty {L : List S} (hL : L ≠ []) : L.reverse ≠ [] := by
  apply List.length_pos.1
  rw [List.length_reverse]
  exact List.length_pos.2 hL

lemma eq_iff_reverse_eq (L1 L2 : List α) : L1.reverse = L2.reverse ↔ L1 = L2 := by
  constructor
  . intro h; rw [←List.reverse_reverse L1, ←List.reverse_reverse L2, h, List.reverse_reverse]
  . intro h; rw [h]

lemma reverse_head (L : List α) (h : L ≠ []) :
  L.reverse = (L.getLast h) :: (L.dropLast).reverse := by
  induction L with
  | nil => contradiction
  | cons hd tail ih =>
    by_cases k : tail = []
    . simp_rw [k]
      simp only [ne_eq, not_true_eq_false, List.reverse_nil, List.dropLast_nil,
        IsEmpty.forall_iff, List.reverse_cons, List.nil_append, List.getLast_singleton',
        List.dropLast_single]
    . push_neg at k
      rw [List.reverse_cons, List.getLast_cons k, List.dropLast, List.reverse_cons, ih k]
      . rfl
      . exact k

lemma dropLast_eq_reverse_tail_reverse {L : List S} : L.dropLast = L.reverse.tail.reverse := by
  induction L with
  | nil => simp only [List.dropLast_nil, List.reverse_nil, List.tail_nil]
  | cons hd tail ih =>
    by_cases k : tail = []
    . rw [k]
      simp only [List.dropLast_single, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.tail_cons]
    . push_neg at k
      have htd : (hd :: tail).dropLast = hd :: (tail.dropLast) := by
        exact List.dropLast_cons_of_ne_nil k
      rw [htd]
      have trht : (tail.reverse ++ [hd]).tail = (tail.reverse.tail) ++ [hd] :=
        List.tail_append_of_ne_nil _ _ (reverseList_nonEmpty k)
      have : (hd :: tail).reverse.tail = (hd :: tail).dropLast.reverse := by
        rw [htd]
        simp only [List.reverse_cons]
        rw [trht]
        apply (List.append_left_inj [hd]).2
        exact List.reverse_eq_iff.1 ih.symm
      rw [this, List.reverse_reverse, htd]

lemma reverse_tail_reverse_append {L : List S} (hL : L ≠ []) :
  L.reverse.tail.reverse ++ [L.getLast hL] = L := by
  rw [← dropLast_eq_reverse_tail_reverse]
  exact List.dropLast_append_getLast hL

--#check reverse_append

--#check dropLast_concat

/-
lemma removeNth_length_sub_one (L:List α) : removeNth L (L.length - 1) = dropLast L :=by sorry

lemma removeNth_concat {a:α} (L:List α) : removeNth (concat L a) L.length = L:=by sorry
-/

--#print List.get?_eq_get

lemma range_map_insert_zero {α : Type u} {n : ℕ} {f : ℕ → α} {g : ℕ → α}
    (h : ∀(i : Fin n), g i = f (i + 1)) :
    (range (n + 1)).map f = (f 0) :: (range n).map g := by
  rw [range_eq_range', ← range'_append 0 1 n 1]
  simp only [range'_one, mul_one, zero_add, singleton_append, map_cons, cons.injEq, true_and]
  rw [range'_eq_map_range, ← List.comp_map]
  ext a b
  simp only [get?_map, Option.mem_def, Option.map_eq_some', Function.comp_apply]
  by_cases ha : a < (range n).length
  · rw [get?_eq_get ha]
    simp only [get_range, Option.some.injEq, exists_eq_left']
    rw [length_range n] at ha
    rw [h ⟨a, ha⟩]
    simp only [add_comm]
  · push_neg at ha
    simp only [get?_eq_none.mpr ha, false_and, exists_const]

lemma take_range {n i : ℕ} (h : i ≤ n) : (List.range n).take i = List.range i := by
  refine (ext_get ?hl ?h).symm
  rw [length_range, length_take, length_range]
  exact eq_min Nat.le.refl h fun {_} a _ => a
  intro m h1 h2
  rw [get_range, ← get_take, get_range]
  rw [length_range] at h1 ⊢
  exact Nat.lt_of_lt_of_le h1 h
  rw [length_range] at h1
  exact h1

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

open BigOperators

section BigOperators

lemma prod_insert_zero_fin {M : Type u} [CommMonoid M] {n : Nat} {f : Fin (n + 1) → M} {g : Fin n → M} (h : ∀(i : Fin n), g i = f i.succ) :
    ∏ i : Fin (n + 1), f i = f 0 * ∏ i : Fin n, g i := by
  set s: Finset (Fin (n + 1)) := Finset.univ \ {0}
  have hs : 0 ∉ s := by simp [s]
  have unions : insert 0 s = Finset.univ := by
    simp [s, Finset.insert_eq]
  calc
    _ = f 0 * ∏ i in s, f i := by
      rw [← unions, Finset.prod_insert hs]
    _ = _ := by
      congr 1
      apply Eq.symm
      apply Finset.prod_nbij Fin.succ
      . intro a _; simp_rw [s]
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        . simp
        . push_neg; simp [Fin.succ_ne_zero]
      . rw [Set.InjOn]; intro _ _ _ _; exact Fin.succ_inj.1
      . rw [Set.SurjOn]; intro i hi; rw [Set.mem_image]
        have nezero : i ≠ 0 := by intro hhi; rw [hhi] at hi; exact hs hi
        obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero nezero
        use j; simp [hj]
      . exact fun i _ ↦ h i

lemma prod_insert_zero {M : Type u} [CommMonoid M] {n : Nat} {f g : Nat → M} (h : ∀(i : Fin n), g i = f (i.val + 1)) :
    ∏ i : Fin (n + 1), f i = f 0 * ∏ i : Fin n, g i := by
  exact prod_insert_zero_fin h

lemma prod_insert_last {M : Type u} [CommMonoid M] (n : Nat) (f : Nat → M) :
    ∏ i : Fin (n + 1), f i = f n * ∏ i : Fin n, f i := by
  let n_fin : Fin (n + 1) := Fin.last n
  set s: Finset (Fin (n + 1)) := Finset.univ \ {n_fin}
  have hs : n_fin ∉ s := by simp [s]
  have unions : insert n_fin s = Finset.univ := by
    simp [s, Finset.insert_eq]
  calc
    _ = f n_fin * ∏ i in s, f i := by
      rw [← unions, Finset.prod_insert hs]
    _ = _ := by
      congr 1
      apply Eq.symm
      apply Finset.prod_nbij Fin.castSucc
      . intro a _; simp_rw [s]
        rw [Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        . simp
        . simp only [n_fin]; exact ne_of_lt (Fin.castSucc_lt_last a)
      . rw [Set.InjOn]; intro _ _ _ _; exact Fin.castSucc_inj.1
      . rw [Set.SurjOn]; intro i hi; rw [Set.mem_image]
        have : i ≠ n_fin := by
          contrapose! hs; rw [hs] at hi; exact hi
        use Fin.castPred i this
        simp
      . exact fun _ _ ↦ rfl

lemma prod_insert_last_fin {M : Type u} [CommMonoid M] (n : Nat) (f : Fin (n + 1) → M) :
    ∏ i : Fin (n + 1), f i = f n * ∏ i : Fin n, f i := by
  let fn : Nat → M := fun x ↦ if h : x < n + 1 then f ⟨x, h⟩ else 1
  calc
    _ = ∏ i : Fin (n + 1), fn i := by
      congr
      ext x
      simp only [fn,Fin.is_lt, reduceDite, Fin.eta]
    _ = fn n * ∏ i : Fin n, fn i := prod_insert_last n fn
    _ = _ := by
      congr
      simp only [fn, if_pos (Nat.le_add_right n 1), lt_add_iff_pos_right,
        zero_lt_one, reduceDite, Fin.cast_nat_eq_last]
      rfl
      ext x
      simp only [Fin.coe_eq_castSucc]
      exact dif_pos (Fin.castLE.proof_1 (Nat.le_add_right n 1) x)

lemma prod_insert_zero_last {M : Type u} [CommMonoid M] (n : Nat) (f : ℕ → M) :
    ∏ i : Fin (n + 2), f i = f 0 * f (n + 1) * ∏ i : Fin n, f (i + 1) := by
  rw [@prod_insert_zero M _ (n + 1) f (fun i ↦ f (i + 1)) (fun i ↦ rfl), mul_assoc]
  congr 1
  exact prod_insert_last n (fun i ↦ f (i + 1))

lemma halve_odd_prod {M : Type u} [CommMonoid M] {n : ℕ} (f : ℕ → M) :
    ∏ i : Fin (2 * n + 1), f i = f n * ∏ i : Fin n, (f i * f (2 * n - i)) := by
  induction n generalizing f with
  | zero =>
    simp only [Nat.zero_eq, Nat.mul_zero, Nat.cast_zero, Finset.univ_eq_empty, Fin.coe_eq_castSucc,
      Fin.reduceMul, zero_sub, Finset.prod_empty, mul_one]
    exact Fintype.prod_subsingleton (fun x : Fin 1 ↦ f x) 0
  | succ m ih =>
    let f' : ℕ → M := fun i ↦ f (i + 1)
    let g : ℕ → M := fun i ↦ f i * f (2 * m + 2 - i)
    calc
      _ = f 0 * f ((2 * m + 1 : ℕ) + 1) * ∏ i : Fin (2 * m + 1), f (i + 1) := by
        rw [← prod_insert_zero_last (2 * m + 1) f]
        rfl
      _ = f 0 * f (2 * m + 1 + 1) * ∏ i : Fin (2 * m + 1), f' i := by rfl
      _ = g 0 * (f' m * ∏ i : Fin m, g (i + 1)) := by
        rw [ih f']
        dsimp only [g]
        congr 3
        ext i
        congr 2
        simp only [Nat.succ_sub_succ_eq_sub,f']
        congr
        rw [Nat.sub_add_comm];
        exact le_trans (Nat.le_of_lt i.2) (@Nat.le_mul_of_pos_left 2 m (by linarith))
      _ = f' m * (g 0 * ∏ i : Fin m, g (i + 1)) := by
        rw [← mul_assoc (f' m), mul_comm (f' m) (g 0), mul_assoc (g 0)]
      _ = f' m * ∏ i : Fin (m + 1), g i := by
        rw [prod_insert_zero_fin (fun i ↦ rfl)]
        rfl
      _ = _ := by dsimp only [f', g]; rfl

end BigOperators


/-The following is about lists of elements in a subset of G-/
section CoeM
universe u
variable {α β : Type u} [(a : α) -> CoeT α a β]

@[simp]
lemma coeM_nil_eq_nil : (([] : List α) : List β) = ([] : List β) := by rfl

@[simp]
lemma coeM_singleton {x : α}: (([x] : List α) : List β) = ([(x : β)] : List β) := by rfl

@[simp]
lemma coeM_cons {hd : α} {tail : List α} :
  ((hd :: tail : List α) : List β) = (hd : β) :: (tail : List β) := by rfl

@[simp]
lemma coeM_append {l1 l2 : List α} :
  ((l1 ++ l2) : List β) = (l1 : List β ) ++ (l2 : List β) := by
  simp only [Lean.Internal.coeM, List.bind_eq_bind, List.append_bind]


@[simp]
lemma coeM_reverse {l : List α} : (l.reverse : List β) = (l : List β ).reverse := by
  induction l with
  | nil => trivial
  | cons hd tail ih => simp only [List.reverse_cons, coeM_append, coeM_cons]; congr

@[simp]
lemma mem_subtype_list {x : α} {S : Set α} {L : List S}: x ∈ (L : List α) → x ∈ S := by {
  intro H
  induction L with
  | nil => trivial
  | cons hd tail ih => {
    simp only [List.bind_eq_bind, List.cons_bind, List.mem_append, List.mem_pure, List.mem_bind,
      Subtype.exists, exists_and_right, exists_eq_right'] at H
    cases H with
    | inl hh => {
      have : CoeT.coe hd = (hd : α) := rfl
      simp only [hh, this, Subtype.coe_prop]
    }
    | inr hh => {
      obtain ⟨y, hy⟩:= hh
      simp only [List.bind_eq_bind, List.mem_bind, List.mem_pure, Subtype.exists, exists_and_right,
        exists_eq_right', forall_exists_index] at ih
      exact ih y hy
      }
  }
}

end CoeM

section list_properties
--open Classical

variable {G : Type _} [Group G] {S : Set G}

--noncomputable instance HasBEq : BEq S where
--  beq := fun s1 s2 => s1.val = s2.val

@[coe]
abbrev List.gprod {S : Set G} (L : List S) := (L : List G).prod

instance List.ListGtoGroup : CoeOut (List G) G where
  coe := fun L ↦ (L : List G).prod

instance List.ListStoGroup : CoeOut (List S) G where
  coe := fun L ↦ L.gprod

@[simp, gprod_simps]
lemma gprod_nil : ([] : List S) = (1 : G) := by exact List.prod_nil

@[simp, gprod_simps]
lemma gprod_singleton {s : S}: ([s] : G) = s := by
  calc
   _ = List.prod [(s : G)] := by congr
   _ = s := by simp

@[simp, gprod_simps]
lemma gprod_eq_of_list_eq {L1 L2 : List S} (h : L1 = L2) : (L1 : G) = (L2 : G) := by rw [h]

-- Some automation regarding List S
--instance HasHMulListList : HMul (List S) (List S) (List S) where
--  hMul := fun L1 L2 ↦ (L1 ++ L2 : List S)

instance HasHMulListS : HMul (List S) S G where
  hMul := fun L g ↦ (L : G) * g

instance HasHMulGList : HMul G (List S) G where
  hMul := fun g L ↦ g * (L : G)

--The following instance will cause wrong type class resolution
--instance HasHMulST {S T: Set G}: HMul S T G where
--  hMul := fun s t ↦ s.val*t.val

@[gprod_simps]
lemma gprod_cons (hd : S)  (tail : List S) : (hd :: tail : G) = hd * (tail : G) := by {
  simp_rw [← List.prod_cons]
  congr
}

@[simp, gprod_simps]
lemma gprod_append {l1 l2 : List S} : (l1 ++ l2 : G) = l1 * l2 := by {
  rw [← List.prod_append]
  congr
  simp [List.gprod, Lean.Internal.coeM]
}

@[simp, gprod_simps]
lemma gprod_append_singleton {l1 : List S} {s : S} : (l1 ++ [s] : G) = l1 * s := by {
  rw [← gprod_singleton, gprod_append]
}

@[simp]
abbrev inv_reverse (L : List S) : List G := (List.map (fun x ↦ (x : G)⁻¹) L).reverse

lemma gprod_inv_eq_inv_reverse (L: List S) : (L : G)⁻¹ = inv_reverse L := by rw [List.prod_inv_reverse]

lemma inv_reverse_prod_prod_eq_one {L: List S} : inv_reverse L * (L : G) = 1 :=
  by rw [inv_reverse, ← gprod_inv_eq_inv_reverse, mul_left_inv]

attribute [gprod_simps] mul_assoc mul_one one_mul mul_inv_rev mul_left_inv mul_right_inv inv_inv inv_one mul_inv_cancel_left inv_mul_cancel_left

namespace Submonoid
variable {M : Type*} {M : Type*} [Monoid M] (T : Set M)


/-
An element is in the submonoid closure of T ⊂ M if and only if it can be
written as a product of elements in T
-/
lemma mem_monoid_closure_iff_prod {M : Type*} [Monoid M] (T : Set M) (z : M) :
  z ∈ closure T ↔ (∃ L : List T, z = (L : List M).prod) := by
    constructor
    . intro hz ; induction' hz using closure_induction' with s hs x _ y _ hx hy x _ hx
      . use [⟨s,hs⟩]; simp [List.prod_singleton,pure,List.pure]
      . use []; simp [List.prod_nil]
      . obtain ⟨Lx,hLx⟩ := hx
        obtain ⟨Ly,hLy⟩ := hy
        use Lx++Ly
        rw [hLx,hLy,<-List.prod_append]
        congr;simp only [List.bind_eq_bind, List.append_bind]
    . rintro ⟨L,hL⟩
      induction' L with x L' ih generalizing z
      . have : z= 1 := by simp only [hL, List.bind_eq_bind, List.nil_bind, List.prod_nil]
        simp only [this, Submonoid.one_mem]
      . have : z = x * (L' : List M).prod := by
          rw [hL,<-List.prod_cons]; congr
        rw [this]
        apply mul_mem
        . exact Set.mem_of_mem_of_subset x.prop Submonoid.subset_closure
        . exact ih (L' : List M).prod rfl

end Submonoid

namespace Subgroup

variable {G :Type*} [Group G] {S : Set G}

local notation "T"=> {z | z∈ S ∨ z⁻¹∈S}

def List.inv.aux (x : T) : x.val⁻¹ ∈ T := by
  cases' x.prop with h h
  . right; rw [inv_inv]; exact h
  . left; exact h

/-
def List.inv (L : List T) : List {z | z∈ S ∨ z⁻¹∈S} :=
  match L with
  | [] => []
  | x :: tail => ⟨x.val⁻¹, List.inv.aux x⟩ :: List.inv tail
-/


def List.inv (L : List T) : List {z | z∈ S ∨ z⁻¹∈S} := L.map (fun z => ⟨z.val⁻¹, List.inv.aux z⟩)

lemma List.inv.coeM (L : List T) : (List.inv L: List G) = (L : List G).map (fun z => z⁻¹) := by
  rw [List.inv]
  induction' L with x t hx
  . trivial
  . calc
    _ = x.val⁻¹ :: List.inv t := by rfl
    _ = _ := by rw [List.inv,hx];rfl


def List.inv_reverse (L : List T) : List T := (List.inv L).reverse

lemma List.inv_eq_inv_reverse (L: List T) : (L : G)⁻¹ = List.inv_reverse L := by
    rw [List.prod_inv_reverse,inv_reverse,List.inv]
    congr
    induction' L with x t hx
    . trivial
    . calc
      _ =  (List.reverse
    (List.map (fun x => x⁻¹) (t:List G))) ++ [x.val⁻¹] := by
        simp only [Set.coe_setOf, Set.mem_setOf_eq, List.bind_eq_bind, List.cons_bind,
          List.map_append, List.reverse_append, List.append_cancel_left_eq];rfl
      _ = _ := by
        simp_rw [hx,Set.coe_setOf, Set.mem_setOf_eq, List.bind_eq_bind, List.map_cons,
          List.reverse_cons, List.append_bind, List.cons_bind, List.nil_bind, List.append_nil,
          List.append_cancel_left_eq]
        rfl

/-
An element is in subgroup closure of S if and only if it can be
written as a product of elements in {z | z ∈ S ∨ z⁻¹ ∈ S}
-/
lemma mem_subgroup_closure_iff_prod (z : G) :
  z ∈ closure S ↔ (∃ (L : List {z | z ∈ S ∨ z⁻¹ ∈ S}), z = L ) := by
  constructor
  . intro hz
    induction' hz using closure_induction' with s hs x _ y _ hx hy x _ hx
    . use [⟨s,Or.inl hs⟩]
      rw [gprod_singleton]
    . use []
      rw [gprod_nil]
    . --intro x y hx hy
      obtain ⟨Lx,hLx⟩ := hx
      obtain ⟨Ly,hLy⟩ := hy
      use Lx++Ly
      rw [hLx,hLy,gprod_append]
    . obtain ⟨L,hL⟩:=hx
      use List.inv_reverse L
      rw [hL,List.inv_eq_inv_reverse]
  . intro ⟨L,hL⟩
    induction' L with x hx thx generalizing z
    . rw [gprod_nil] at hL
      simp only [hL,Subgroup.one_mem]
    . rw [gprod_cons] at hL
      rw [hL]
      apply mul_mem
      . cases x.prop with
        | inl h => exact Set.mem_of_mem_of_subset h Subgroup.subset_closure
        | inr h =>
          apply (Subgroup.inv_mem_iff _).1
          exact Set.mem_of_mem_of_subset h Subgroup.subset_closure
      . exact thx (hx.gprod) (rfl)


end Subgroup



end list_properties

section Sublist

namespace List

variable {α : Type*} [DecidableEq α]

/-
Return the index list of the longest sublist of l' in l with respect to the greedy algorithm

example:
#eval indices_of [1,2,3] [4,5,1,2,0,4,1,2,3]
returns [2,3,8]
-/
def indices_of (l' : List α) (l : List α) : List (Fin l.length)
  := match l', l with
  | _, [] => []
  | [], _ => []
  | x::xs, y::ys =>
    if x = y then
      ⟨0, by simp⟩  :: List.map (Fin.succ) (indices_of xs ys)
    else
      List.map (Fin.succ) (indices_of l' ys)

lemma indices_of_increasing (l' : List α) (l : List α) : (indices_of l' l).Pairwise (·  < ·) := by
  induction' l with y ys ih generalizing l'
  . simp [indices_of]
  . match l' with
    | [] => simp [indices_of]
    | x::xs =>
      rw [indices_of]
      by_cases h : x = y
      . rw [if_pos h,pairwise_cons]
        constructor <;> simp [pairwise_map,ih xs]
      . simp [if_neg h,pairwise_map, ih (x::xs)]

lemma ne_cons_sublist {a b : α} (h: a≠ b) : a :: l' <+ b::l → a::l' <+ l := by
  intro hl
  rcases hl
  . assumption
  . contradiction

lemma sublist_eq_map_get_index_of {l' l : List α } (h : l' <+ l) : l' = map (get l) (indices_of l' l) := by
  induction' l with y ys ih generalizing l'
  . simp only [sublist_nil.1 h, length_nil, indices_of, map_nil]
  . match l' with
    | [] => simp [indices_of]
    | x::xs =>
      rw [indices_of]
      by_cases hxy: x=y
      . rw [hxy] at h
        have h' : xs <+ ys := cons_sublist_cons.1 h
        simp_rw [if_pos hxy,map_cons,hxy,map_map]
        nth_rw 1 [ih h']
        congr
      . rw [if_neg hxy]
        have h' : x::xs <+ ys := ne_cons_sublist hxy h
        have ih := ih h'
        rw [map_map,ih]
        congr

def complement_indices_of' (l':List α) (l:List α) : List (Fin l.length) := List.filter (fun x => x ∉ indices_of l' l) (Fin.list l.length)

end List


end Sublist

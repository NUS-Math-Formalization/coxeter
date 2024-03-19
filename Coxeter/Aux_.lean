import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.List.Range
import Mathlib.Algebra.Module.Equiv
import Mathlib.Data.List.Palindrome
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Logic.Equiv.Fin

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

/-map and removeNth are commute with each other-/
lemma map_removeNth_comm {α : Type*} {β : Type*} {f : α → β } (L : List α) (i : ℕ)
: (L.removeNth i).map f = (L.map f).removeNth i := by sorry

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

lemma reverse_drop {α : Type _} (L : List α) (n : ℕ) : (L.drop n).reverse = L.reverse.take (L.length - n) := by
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
        simp only [removeNth, Nat.add_eq, add_zero, cons.injEq, true_and]
        apply ih'
        exact Nat.lt_succ.1 (Nat.le.step h)
        simp only [removeNth, Nat.add_eq, add_zero, cons.injEq, true_and] at ih
        apply ih
  nth_rw 2 [← remove_after_L_length']
  rw [Nat.sub_add_cancel h]

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

#print List.get?_eq_get

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

lemma prod_insert_zero_fin {M : Type u} [CommMonoid M] {n : Nat} {f : Fin (n + 1) → M} {g : Fin n → M} (h : ∀(i : Fin n), g i = f ⟨i.val + 1, add_lt_add_right i.prop 1⟩) :
    ∏ i : Fin (n + 1), f i = f 0 * ∏ i : Fin n, g i := by
  let not0 : Set (Fin (n + 1)) := Set.univ \ {0}
  have no0 : 0 ∉ not0 := Set.not_mem_diff_of_mem rfl
  let plus1 : (Fin n) → (Fin (n + 1)) := fun x ↦ ⟨x.val + 1, (by linarith [x.prop])⟩
  calc
    _ = ∏ᶠ (i : Fin (n + 1)) (_ : i ∈ Set.univ), f i := by
      rw [finprod_eq_prod_of_fintype]
      congr
      ext x
      simp only [Set.mem_univ x, finprod_true]
    _ = f 0 * ∏ᶠ (i : Fin (n + 1)) (_ : i ∈ not0), f i := by
      have prod_insert := finprod_mem_insert (fun i : Fin (n + 1) ↦ f i) no0 (Set.toFinite not0)
      have insert0 : insert 0 not0 = Set.univ := by
        ext x
        constructor
        · exact fun _ ↦ Set.mem_univ x
        · exact fun _ ↦
            if h : x = 0 then Set.mem_insert_iff.mpr (Or.inl h)
            else Set.mem_insert_of_mem 0 ⟨Set.mem_univ x, h⟩
      rw [insert0] at prod_insert
      rw [prod_insert]
    _ = f 0 * ∏ᶠ (i : Fin (n + 1)) (_ : i ∈ plus1 '' Set.univ), f i := by
      have : not0 = plus1 '' Set.univ := by
        ext x
        constructor
        · rintro ⟨_, hx⟩
          set! xv := x.val with hxv
          have : xv ≠ 0 := (Fin.ne_iff_vne x 0).mp hx
          rcases xv with (_ | x')
          · exact (this rfl).elim
          · have : x' < n := by
              apply Nat.lt_of_succ_lt_succ
              rw [hxv]
              exact x.2
            use ⟨x', this⟩
            simp only [plus1]
            exact ⟨Set.mem_univ (⟨x', this⟩ : Fin n), (Fin.eq_iff_veq _ _).mpr hxv⟩
        · rintro ⟨y, ⟨_, gyx⟩⟩
          have : y.val + 1 = x := (Fin.eq_iff_veq _ _).mp gyx
          rw [← Nat.succ_eq_add_one] at this
          have : x.val ≠ 0 := by
            rw [← this]
            exact Nat.succ_ne_zero y.val
          exact ⟨Set.mem_univ x, (Fin.ne_iff_vne _ _).mpr this⟩
      rw [this]
    _ = f 0 * ∏ᶠ (i : Fin n) (_ : i ∈ Set.univ), f (plus1 i) := by
      have : Set.InjOn plus1 Set.univ := by
        intro a _ b _ hab
        simp only [plus1] at hab
        exact (Fin.eq_iff_veq a b).mpr (Nat.add_right_cancel ((Fin.eq_iff_veq _ _).mp hab))
      rw [finprod_mem_image this]
    _ = f 0 * ∏ i : Fin n, g i := by
      rw [finprod_eq_prod_of_fintype]
      congr
      ext x
      simp only [Set.mem_univ x, finprod_true]
      exact (h x).symm

lemma prod_insert_zero {M : Type u} [CommMonoid M] {n : Nat} {f g : Nat → M} (h : ∀(i : Fin n), g i = f (i.val + 1)) :
    ∏ i : Fin (n + 1), f i = f 0 * ∏ i : Fin n, g i := by
  exact prod_insert_zero_fin h

lemma prod_insert_last {M : Type u} [CommMonoid M] (n : Nat) (f : Nat → M) :
    ∏ i : Fin (n + 1), f i = f n * ∏ i : Fin n, f i := by
  repeat rw [← finprod_eq_prod_of_fintype]
  let n_fin : Fin (n + 1) := ⟨n, Nat.le.refl⟩
  let not_n : Set (Fin (n + 1)) := Set.univ \ {n_fin}
  have no_n : n_fin ∉ not_n := Set.not_mem_diff_of_mem rfl
  have prod_insert := finprod_mem_insert (fun i : Fin (n + 1) ↦ f i) no_n (Set.toFinite not_n)
  have insert_n : insert n_fin not_n = Set.univ := by
    ext x
    constructor
    · exact fun _ ↦ Set.mem_univ x
    · exact fun _ ↦
        if h : x = n_fin then Set.mem_insert_iff.mpr (Or.inl h)
        else Set.mem_insert_of_mem n_fin ⟨Set.mem_univ x, h⟩
  rw [insert_n] at prod_insert
  simp only [Set.mem_univ, finprod_true] at prod_insert
  rw [prod_insert]
  congr 1
  let fmap : Fin n → Fin (n + 1) := fun x ↦ ⟨x.1, (by linarith [x.2] : x.1 < n + 1)⟩
  have : Set.InjOn fmap Set.univ := by
    intro a _ b _ hab
    simp only [fmap] at hab
    exact (Fin.eq_iff_veq a b).mpr ((@Fin.eq_iff_veq (n + 1) _ _).mp hab)
  have := @finprod_mem_image _ _ M _ (fun x ↦ f x.1) Set.univ fmap this
  simp only [Set.mem_univ, finprod_true] at this
  rw [← this]
  congr
  ext x
  have : not_n = fmap '' Set.univ := by
    ext x
    constructor
    · rintro ⟨_, hx⟩
      have : x.1 < n := Fin.val_lt_last hx
      use ⟨x.1, this⟩
      simp only [fmap]
      exact And.intro (Set.mem_univ _) True.intro
    · rintro ⟨y, ⟨_, gyx⟩⟩
      have : x.val ≠ n := by
        rw [← (Fin.eq_iff_veq _ _).mp gyx]
        exact Nat.ne_of_lt y.2
      exact ⟨Set.mem_univ x, (Fin.ne_iff_vne _ _).mpr this⟩
  rw [← this]

lemma prod_insert_last_fin {M : Type u} [CommMonoid M] (n : Nat) (f : Fin (n + 1) → M) :
    ∏ i : Fin (n + 1), f i = f n * ∏ i : Fin n, f i := by
  let fn : Nat → M := fun x ↦ if h : x < n + 1 then f ⟨x, h⟩ else 1
  calc
    _ = ∏ i : Fin (n + 1), fn i := by
      congr
      ext x
      simp only [Fin.is_lt, reduceDite, Fin.eta]
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
        simp only [Nat.succ_sub_succ_eq_sub]
        ring_nf
        exact (Nat.add_sub_assoc (by linarith [i.2]) 1).symm
      _ = f' m * (g 0 * ∏ i : Fin m, g (i + 1)) := by
        rw [← mul_assoc (f' m), mul_comm (f' m) (g 0), mul_assoc (g 0)]
      _ = f' m * ∏ i : Fin (m + 1), g i := by
        rw [prod_insert_zero_fin (fun i ↦ rfl)]
        rfl
      _ = _ := by dsimp only [f', g]; rfl

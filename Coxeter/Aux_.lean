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
import Mathlib.Data.List.Palindrome
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Logic.Equiv.Fin

import Coxeter.AttrRegister

import Ssreflect.Lang

namespace List
variable {α : Type _} [BEq α] [Inhabited α]

/-- Appending an element on a list makes it nonempty. -/
lemma append_singleton_ne_nil (L : List α) (a : α) : L ++ [a] ≠ [] := by
  elim: L => //

/-- The length of a list prepended with an element is one more than that of
the original list. -/
lemma length_hd_tail_eq_succ_length (L : List α) (a : α)
: (a :: L).length = L.length + 1 := by move=>//

/-- Removing the last element of a list appended with an element undoes the
append. -/
lemma append_remove_cancel_of_eq_last_index {a : α} {n : ℕ} (h : n = L.length)
: (L ++ [a]).removeNth n = L := by
  elim: L n => //

/-- The length of a list appended with an element is one more than that of
the original list. -/
lemma length_append_singleton (L : List α) (a : α)
: (L ++ [a]).length = L.length + 1 := by
  elim: L => //

/-- The length of `L.take n` is exactly n if `L` has at least n elements. -/
lemma take_le_length (L : List α) (h : n ≤ L.length)
: (L.take n).length = n := by move=>//

/-- `map` and `removeNth` commute with each other-/
lemma map_removeNth_comm
{α : Type*} {β : Type*} {f : α → β } (L : List α) (i : ℕ)
: (L.removeNth i).map f = (L.map f).removeNth i := by
  move: i
  elim: L => //
  move=> h t ih
  elim=> //

/-- Removing the n'th element of a list is the same as taking the first n
elements and all the elements after the n'th. -/
lemma removeNth_eq_take_drop {α : Type _} (L: List α) (n : ℕ)
: L.removeNth n = L.take n ++ L.drop (n+1) := by
  revert n
  elim: L => //
  move=> hd tl ih n
  elim: n => //

/-- Removing the n'th element of a list is the same as taking the first n
elements and all the elements after the n'th. -/
@[deprecated removeNth_eq_take_drop]
lemma remove_nth_eq_take_drop {α : Type _} (L: List α) (n : ℕ)
: L.removeNth n = L.take n ++ L.drop (n+1) := by
  exact removeNth_eq_take_drop L n

/-- If `n < L.length` then the length of `L.removeNth n` is one less than the
original list. -/
lemma removeNth_length {α : Type _} (L: List α) (n : Fin L.length)
: (L.removeNth n).length + 1 = L.length := by
  elim: L => //==
  move => h t hi n
  match n.val, n.prop with
  | 0, _ => move=>//
  | m + 1, nprop =>
    rw [removeNth, length]; exact hi ⟨m, (add_lt_add_iff_right 1).mp nprop⟩

/-- Reversing `L.drop n` is equal to taking the first `L.length - n` elements
of the reverseal of the original list. -/
lemma reverse_drop {α : Type _} (L : List α) (n : ℕ)
: (L.drop n).reverse = L.reverse.take (L.length - n) := by
  move: n
  elim: L => //
  move => h t ih
  elim=> //
  simp only [Nat.zero_eq, drop_zero, reverse_cons, tsub_zero]
  rw [← length_reverse, reverse_cons, take_length]
  move=> n _
  simp only [drop_succ_cons, length_cons, Nat.succ_sub_succ_eq_sub,
    reverse_cons]
  rw [ih, take_append_of_le_length]
  rw [length_reverse]
  simp

/-- For any nonzero natural n, `n - 1 < n.` -/
lemma sub_one_lt_self (n: ℕ) (_ : 0 < n) : n - 1 < n := by elim: n=>//

lemma take_drop_get {α : Type _} (L: List α) (n : ℕ) (h : n < L.length):
  L = L.take n ++ [L.get ⟨n,h⟩] ++ L.drop (n+1) := by
  have Hn :=  List.take_append_drop n L
  have Hd := List.drop_eq_get_cons h
  rw [Hd] at Hn
  simp only [append_assoc, singleton_append, Hn]

/-- Dropping n elements after taking n elements yields an empty list. -/
@[simp]
lemma drop_take_nil {α : Type _} {L : List α} {n : ℕ}
: (L.take n).drop n = [] := by
  exact drop_length_le (length_take_le n L)

/-- For a list with more than n elements, taking the first n+1 elements is
the same as taking the first n elements and appending the n+1'th element. -/
lemma take_get_lt {α : Type _} (L: List α) (n : ℕ) (h : n < L.length)
: L.take (n+1) = L.take n ++ [L.get ⟨n, h⟩] := by
  have h1 : L = L.take n ++ [L.get ⟨n, h⟩] ++ L.drop (n+1) :=
    take_drop_get L n h
  have h2 : L = L.take (n+1) ++ L.drop (n+1) :=
    symm (take_append_drop (n+1) L)
  nth_rw 1 [h2] at h1
  exact (append_left_inj (drop (n+1) L)).mp h1

/-- Assuming n < L.length, the output of L.get and L.nthLe is equal. -/
lemma get_eq_nthLe {α : Type _} {L: List α} {n : ℕ} {h : n < L.length} :
  L.get ⟨n, h⟩ = L.nthLe n h := by rfl

/-- if n < L1.length then removing the n'th element from L1++L2 is the same as
appending L2 to L1 with the n'th element removed. -/
@[simp]
lemma removeNth_append_lt
{α : Type _} (L1 L2: List α) (n : ℕ) (h : n < L1.length)
: (L1 ++ L2).removeNth n = L1.removeNth n ++ L2 := by
  rw [removeNth_eq_take_drop, removeNth_eq_take_drop]
  rw [List.take_append_of_le_length (le_of_lt h)]
  have : (L1 ++ L2).drop (n + 1) = L1.drop (n + 1) ++ L2 :=
    drop_append_of_le_length (by linarith)
  rw [this, append_assoc]

/-- removeNth does nothing if the index is larger than the length of the list.
-/
lemma remove_after_L_length (L : List α) {i : ℕ} (h : L.length ≤ i)
  : L.removeNth i = L := by
  revert i
  elim: L => //=
  move=> h t ih jh
  unfold removeNth
  split
  move=> j //
  specialize ih (by linarith)
  rename_i s
  rw [head_eq_of_cons_eq s]; rw [tail_eq_of_cons_eq s] at *; rw [ih]

/-- Taking the first i elements after removing the j'th element for j > i is
the same as taking the first i elements. -/
lemma take_of_removeNth (L : List α) {i j : ℕ} (h : i ≤ j) :
    (L.removeNth j).take i = L.take i := by
  scase: [j < L.length] => //==
  move=> d
  rw [remove_after_L_length L d]
  rw [removeNth_eq_take_drop]
  have : (L.take j).length = j := take_le_length L (by linarith)
  have i_le_j' : i ≤ (L.take j).length := by linarith
  have : L.take i = (L.take j).take i := by
    srw -[1] (min_eq_left h) => /[tac apply Eq.symm] /[tac apply take_take]
  rw [this]
  exact take_append_of_le_length i_le_j'

/-- Removing the n'th element after reversing the list is the same as reversing
the list after removing the `L.length - n - 1`θ element for n not out of
bounds. -/
lemma removeNth_reverse (L : List α) (n : ℕ) (h : n < L.length) :
  (L.reverse).removeNth n = (L.removeNth (L.length - n - 1)).reverse := by
  rw [removeNth_eq_take_drop, removeNth_eq_take_drop]
  rw [List.reverse_append, List.reverse_take n (Nat.le_of_lt h), Nat.sub_sub]
  nth_rw 6 [←List.reverse_reverse L]; nth_rw 7 [←List.reverse_reverse L]
  rw [List.length_reverse L.reverse]
  rw [List.reverse_take (length (reverse L) - (n + 1))
    (Nat.sub_le L.reverse.length (n+1)),
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

/-- Reversing L++[a] is the same as prepending a to the reverse of L. -/
lemma reverse_cons'' (L : List α) (a : α)
: (L ++ [a]).reverse = a :: L.reverse := by
  rw [List.reverse_append, List.reverse_singleton]; simp;

/-- Two lists are equal iff their reversals are equal. -/
lemma eq_iff_reverse_eq (L1 L2 : List α)
: L1.reverse = L2.reverse ↔ L1 = L2 := by move => //

/-- If g(i) = f(i + 1) then mapping f to [0,...,n] is the same as f(0)
prepended to mapping g on [0,...,n-1]. -/
lemma range_map_insert_zero {α : Type u} {n : ℕ} {f : ℕ → α} {g : ℕ → α}
(h : ∀(i : Fin n), g i = f (i + 1))
: (range (n + 1)).map f = (f 0) :: (range n).map g := by
  rw [range_eq_range', ← range'_append 0 1 n 1]
  simp only [range'_one, mul_one, zero_add, singleton_append, map_cons,
    cons.injEq, true_and]
  rw [range'_eq_map_range, ← List.comp_map]
  ext a b
  simp only [get?_map, Option.mem_def, Option.map_eq_some',
    Function.comp_apply]
  scase: [a ≥ (range n).length]
  move=> ha
  . push_neg at ha
    rw [get?_eq_get (by linarith)]
    simp only [get_range, Option.some.injEq, exists_eq_left']
    rw [length_range n] at ha
    rw [h ⟨a, ha⟩]
    simp only [add_comm]
  · simp only [get?_eq_none.mpr ha, false_and, exists_const]

/-- The first i elements of a `range n` is a `range i`.-/
lemma take_range {n i : ℕ} (h : i ≤ n)
: (List.range n).take i = List.range i := by
  refine (ext_get ?hl ?h).symm
  rw [length_range, length_take, length_range]
  exact eq_min Nat.le.refl h fun {_} a _ => a
  srw [1] (get_range) (get_take') //==

end List


namespace Nat

lemma pos_of_lt {i n: Nat} (h : i < n) : 0 < n := by elim: n => //

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
            exact ⟨Set.mem_univ (⟨x', this⟩ : Fin n), Fin.ext_iff.mpr hxv⟩
        · rintro ⟨y, ⟨_, gyx⟩⟩
          have : y.val + 1 = x := Fin.ext_iff.mp gyx
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
        exact (@Fin.ext_iff _ a b).mpr (Nat.add_right_cancel (Fin.ext_iff.mp hab))
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
  let fmap : Fin n → Fin (n + 1) :=
    fun x ↦ ⟨x.1, (by linarith [x.2])⟩
  have : Set.InjOn fmap Set.univ := by
    intro a _ b _ hab
    simp only [fmap] at hab
    exact (@Fin.ext_iff _ a b).mpr ((@Fin.ext_iff (n + 1) _ _).mp hab)
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
        rw [← Fin.ext_iff.mp gyx]
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
        ring_nf; congr
        exact (Nat.add_sub_assoc (by linarith [i.2]) 1).symm
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

lemma coeM_nil_eq_nil : (([] : List α) : List β) = ([] : List β) := by rfl

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

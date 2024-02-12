import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.List.Range
import Mathlib.Algebra.Module.Equiv

-- set_option trace.Meta.Tactic.simp.rewrite true
/-
variable {G : Type _} {S : Set G}

#check Coe (List ↑S) (List G)

def mapList : List (↑S) → List G
| []    => []
| a:: as => a.val :: mapList as

instance (priority := low) list_coe {G : Type _} {S : Set G} : CoeTC (List (↑S)) (List G) where
coe (L : List ↑S) := @mapList G S L

lemma coe_eq_coe  {hd : ↑S} {tail :   List ↑S} : (hd :: tail : List G) = hd.1 :: (tail : List G) := by {
  simp
}
-/



namespace  List
variable {α : Type _} [BEq α] [Inhabited α]

lemma append_singleton_ne_nil (L : List α) (a : α) : L ++ [a] ≠ [] := by {
  induction L with
  | nil => {simp}
  | cons hd tail ih => {simp}
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
  | cons hd tail ih => simp

#check length_removeNth


lemma take_le_length (L : List α) (h : n ≤ L.length)  : (L.take n).length = n := by
  simp only [length_take,ge_iff_le, h, min_eq_left]



lemma remove_nth_eq_take_drop {α : Type _} (L: List α) (n : ℕ) : L.removeNth n = L.take n ++ L.drop (n+1) :=
by {
  revert n
  induction L with
  | nil => {intro n; simp only [removeNth, take_nil, drop, append_nil]}
  | cons hd tail ih => {
      intro n
      match n with
      | 0 => {simp only [removeNth, take, drop, nil_append]}
      | k+1 => {
        simp only [removeNth, Nat.add_eq, add_zero, take, drop, cons_append, cons.injEq, true_and]
        exact ih k
      }
   }
}

lemma sub_one_lt_self (n: ℕ) (h : 0 < n) : n - 1 < n := match n with
| 0 => by {contradiction}
| n+1 => by {simp}


lemma take_drop_get {α : Type _} (L: List α) (n : ℕ) (h : n < L.length):
  L = L.take n ++ [L.get ⟨n,h⟩] ++ L.drop (n+1) := by {
  have Hn :=  List.take_append_drop n L
  have Hd := List.drop_eq_get_cons h
  rw [Hd] at Hn
  simp only [append_assoc, singleton_append, Hn]
}

@[simp]
lemma drop_take_nil {α : Type _} {L : List α} {n : ℕ} : (L.take n).drop n = [] := by {
  have h:= drop_take n 0 L
  simp only [add_zero, take] at h
  exact h
}

lemma take_get_lt {α : Type _} (L: List α) (n : ℕ) (h : n < L.length) :
  L.take (n+1) = L.take n ++ [L.get ⟨n,h⟩] := by
  have H1 : (L.take (n+1)).length = n+1 := by
    rw [List.length_take]; simp only [ge_iff_le, min_eq_left_iff]; linarith
  have Hn := take_drop_get (L.take (n+1)) n (by linarith)
  sorry
  -- have nn1 : min n (n+1) = n := by simp only [ge_iff_le, le_add_iff_nonneg_right, min_eq_left]
  -- simp only [drop_take_nil, append_nil,take_take,nn1] at Hn
  -- have nn2 : n < n+1 := by simp only [lt_add_iff_pos_right]
  -- have Hgt := get_take L h nn2
  -- rw [Hn,Hgt]


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
  rw [remove_nth_eq_take_drop, remove_nth_eq_take_drop]
  rw [List.take_append_of_le_length (le_of_lt h)]
  have : (L1 ++ L2).drop (n + 1) = L1.drop (n + 1) ++ L2 :=
    drop_append_of_le_length (by linarith)
  rw [this, append_assoc]

-- lemma removeNth_append_ge {α : Type _} (L1 L2: List α) (n : ℕ) (h : n ≥ L1.length) :
--   (L1 ++ L2).removeNth n = L1 ++ L2.removeNth (n - L1.length) := by
--   rw [remove_nth_eq_take_drop, remove_nth_eq_take_drop]
--   rw [List.take_append_of_le_length (le_of_ge h)]



lemma removeNth_reverse (L : List α) (n : ℕ) (h : n < L.length) :
  (L.reverse).removeNth n = (L.removeNth (L.length - n - 1)).reverse := by
  rw [remove_nth_eq_take_drop, remove_nth_eq_take_drop]
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

lemma removeNth_length_sub_one (L:List α) : removeNth L (L.length - 1) = dropLast L :=by sorry

lemma removeNth_concat {a:α} (L:List α) : removeNth (concat L a) L.length = L:=by sorry

def toReflection_i  (L : List S) (i : Fin L.length) := (List.take i.val L) ++ [List.get L i] ++ (List.reverse (List.take i.val L))

def toReflection (L : List S) : Set (List S):= (toReflection_i L)'' Set.univ
end List


section adjoin

set_option checkBinderAnnotations false
universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R A] [Algebra S A] [Algebra R B]
variable {s t : Set A}

-- lemma adjoin_comm_of_generator_set_comm : ∀ a∈s, ∀b∈t ,a*b=b*a →

end adjoin


lemma LinearEquiv_invFun_comp_Fun (R:Type u) [Semiring R][AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂](e:M ≃ₗ[R] M₂) : e.invFun ∘ e =id :=by{
  apply Function.LeftInverse.id
  exact e.left_inv
}


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

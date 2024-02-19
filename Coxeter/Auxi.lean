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

-- @[specialize] def groupBy (R : α → α → Bool) : List α → List (List α)
--   | []    => []
--   | a::as => loop as a [] []
-- where
--   @[specialize] loop : List α → α → List α → List (List α) → List (List α)
--   | a::as, ag, g, gs => match R ag a with
--     | true  => loop as a (ag::g) gs
--     | false => loop as a [] ((ag::g).reverse::gs)
--   | [], ag, g, gs => ((ag::g).reverse::gs).reverse

namespace  List
variable {α : Type _} {L : List α}

def cancel_twice [BEq α]: List α → List α
  | [] => []
  | a :: as => loop a as []
where
  loop : α → List α → List α → List α
    | a, [], bl => (a :: bl).reverse
    | a, x :: [], bl => match a == x with
      | true =>  bl.reverse
      | false => (x :: a :: bl).reverse
    | a, x :: (y :: xs), bl => match a == x with
      | true => loop y xs bl
      | false => loop x (y :: xs) (a::bl)

#eval cancel_twice [1,1]
#eval cancel_twice [1,1,1,1]
#eval cancel_twice  [1, 1, 2, 2, 2, 3, 2]
#eval cancel_twice  [1, 2, 5, 5, 1, 4]


lemma take_le_length (L : List α) (h : n ≤ L.length)  : (L.take n).length = n := by
  simp only [length_take,ge_iff_le, h, min_eq_left]

lemma remove_nth_eq_take_drop {α : Type _} (L: List α) (n : ℕ) : L.removeNth n = L.take n ++ L.drop (n+1) :=
by
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

lemma sub_one_lt_self (n: ℕ) ( _ : 0 < n) : n-1 < n := match n with
| 0 => by {contradiction}
| n+1 => by {simp}


lemma take_drop_get {α : Type _} (L: List α) (n : ℕ) (h : n < L.length):
  L = L.take n ++ [L.get ⟨n,h⟩ ] ++ L.drop (n+1) := by
  have Hn :=  List.take_append_drop n L
  have Hd := List.drop_eq_get_cons h
  rw [Hd] at Hn
  simp only [append_assoc, singleton_append, Hn]

@[simp]
lemma drop_take_nil {α : Type _} {L : List α} {n : ℕ} : (L.take n).drop n = [] := by
  have h:= drop_take n 0 L
  simp only [add_zero, take] at h
  exact h

lemma take_get_lt {α : Type _} (L: List α) (n : ℕ) (h : n < L.length): L.take (n+1) = L.take n ++ [L.get ⟨n,h⟩ ] := by {
  have H1 : (L.take (n+1)).length = n+1 := by
    rw [List.length_take]
    simp only [ge_iff_le, min_eq_left_iff]
    linarith
  have Hn := take_drop_get (L.take (n+1)) n (by linarith)
  sorry
  -- have nn1 : min n (n+1) = n := by simp only [ge_iff_le, le_add_iff_nonneg_right, min_eq_left]
  -- simp only [drop_take_nil, append_nil,take_take,nn1] at Hn
  -- have nn2 : n < n+1 := by simp only [lt_add_iff_pos_right]
  -- have Hgt := get_take L h nn2
  -- rw [Hn,Hgt]
}


lemma get_eq_nthLe {α : Type _} {L: List α} {n : ℕ} {h : n < L.length} : L.get ⟨n,h⟩ = L.nthLe n h := by rfl


/-

lemma take_drop_nth_le {α : Type _} (L: List α) (n : ℕ) (h : n < L.length): L = L.take n ++ [L.nthLe n h] ++ L.drop (n+1) := by {
  have := take_drop_get L n h
  rw [List.nthLe_eq]
  exact this
}
-/

lemma removeNth_append_lt {α : Type _} (L1 L2: List α) (n : ℕ) (h : n < L1.length) :
(L1 ++ L2).removeNth n = L1.removeNth n ++ L2 := by {
  rw [remove_nth_eq_take_drop,remove_nth_eq_take_drop,List.take_append_of_le_length (le_of_lt h)]
  have : (L1 ++ L2).drop (n+1) = L1.drop (n+1) ++ L2 := drop_append_of_le_length (by linarith)
  rw [this,append_assoc]
}

#check dropLast_concat

lemma removeNth_length_sub_one (L:List α) : removeNth L (L.length-1) = dropLast L :=by sorry

lemma removeNth_concat {a:α} (L:List α) : removeNth (concat L a) L.length = L:=by sorry

def toReflection_i  (L : List S) (i : Fin L.length) := (List.take i.val L) ++ [List.get L i] ++ (List.reverse (List.take i.val L))

def toReflection (L : List S) : Set (List S):= (toReflection_i L)'' Set.univ

def palindrome := {L : List α // Palindrome L}

def palindrome.mk (L : List α) : @palindrome α := sorry

#check Palindrome
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

import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.List.Range

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
variable {α : Type _}

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

lemma sub_one_lt_self (n: ℕ) (h :0 < n) : n-1 < n := match n with
| 0 => by {contradiction}
| n+1 => by {simp}


lemma take_drop_get {α : Type _} (L: List α) (n : ℕ) (h : n < L.length):
  L = L.take n ++ [L.get ⟨n,h⟩ ] ++ L.drop (n+1) := by {
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

lemma take_get_lt {α : Type _} (L: List α) (n : ℕ) (h : n < L.length): L.take (n+1) = L.take n ++ [L.get ⟨n,h⟩ ] := by {
  have H1 : (L.take (n+1)).length = n+1 := by {rw [List.length_take]; simp only [ge_iff_le, min_eq_left_iff];linarith }
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

end List

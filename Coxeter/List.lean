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
  have nn1 : min n (n+1) = n := by simp only [ge_iff_le, le_add_iff_nonneg_right, min_eq_left]
  simp only [drop_take_nil, append_nil,take_take,nn1] at Hn
  have nn2 : n < n+1 := by simp only [lt_add_iff_pos_right] 
  have Hgt := get_take L h nn2   
  rw [Hn,Hgt]
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



variable {G : Type _} {A : Type _} [Group G] [SetLike A G] {S : A}


@[simp]
def List.gprod {S : A} (L : List S) := (L : List G).prod 

namespace Subgroup
section ProdList 

@[simp]
lemma coe_length_eq {S : A} {L: List S} :
L.length = (L : List G).length := by 
{
  induction L with 
  | nil => {rfl} 
  | cons hd tail ih => {
    rw [List.length_cons, ih] 
    rfl 
  }
}  

@[simp]
lemma nil_eq_nil: (([]: List S) : List G) = [] := by rfl

@[simp]
lemma coe_cons {hd : S}  {tail : List S} : (Lean.Internal.coeM (hd::tail) : List G) = (hd : G) :: (Lean.Internal.coeM tail : List G) := by {
  rfl
}

@[simp]
lemma coe_append  {l1 l2: List S} : (Lean.Internal.coeM (l1 ++ l2): List G) = (Lean.Internal.coeM l1 : List G) ++ (Lean.Internal.coeM l2 : List G):= by {
  simp [Lean.Internal.coeM] 
}

lemma mem_coe_list {x : G} {L : List S}: x ∈ (Lean.Internal.coeM L : List G) → x ∈ S := by {
  intro H 
  induction L with 
  | nil => trivial
  | cons hd tail ih => {
    rw [coe_cons,List.mem_cons] at H
    cases H with 
    | inl hh => {simp [hh]} 
    | inr hh => {exact ih hh}
  } 
}    

lemma nil_gprod : ([]: List S).gprod = 1 := by rfl 

lemma gprod_cons {hd : S}  {tail : List S} : (hd::tail).gprod = hd * (tail.gprod) := by {
  rw [List.gprod,List.gprod,<-List.prod_cons]
  congr
}

lemma gprod_append {l1 l2: List S} : (l1 ++ l2).gprod = l1.gprod * l2.gprod := by {
  rw [List.gprod,List.gprod,List.gprod,<-List.prod_append] 
  congr
  simp [Lean.Internal.coeM]
}

lemma gprod_singleton {s : S}: [s].gprod = s := by 
 rw [List.gprod, coe_cons, nil_eq_nil, List.prod_cons, List.prod_nil, mul_one] 

lemma gprod_append_singleton {l1 : List S} {s : S}: (l1 ++ [s]).gprod = l1.gprod * s := by {
  rw [<-gprod_singleton,gprod_append] 
}

@[simp]
def eqSubsetProd (S : A) (g : G):=    ∃ (L : List S),  g = L.gprod 
 
-- #check eqSubsetProd

lemma mem_SubsetProd  (g : S) : eqSubsetProd S ↑g := by {
   use [g]
   norm_num
} 


lemma mem_one_SubsetProd :  eqSubsetProd S 1 := by {
   use []
   rw [List.gprod, nil_eq_nil, List.prod_nil] 
}

/-
lemma memProd_singleton (x : S) : (x : G) ∈ Subgroup.closure (S : Set G) := by {
   apply Subgroup.subset_closure x.2
}
-/

lemma memProd_singleton : ∀ x :S,  eqSubsetProd S (x : G) := by {
  intro x
  use [x]
  rw [List.gprod, coe_cons, nil_eq_nil, List.prod_cons, List.prod_nil, mul_one]
}


lemma memProd_singleton'  : ∀ x :G, x∈ (S: Set G)  →  eqSubsetProd S (x : G) := by {
  intro x hx
  use [(⟨x, hx⟩:S)]
  rw  [List.gprod, coe_cons, nil_eq_nil, List.prod_cons, List.prod_nil, mul_one] 
}

lemma memProd_one : eqSubsetProd S (1 : G) := by {
  use []
  rw [List.gprod, nil_eq_nil, List.prod_nil] 
}

lemma memProdSubgroupClosure (L : List S) : L.gprod ∈ Subgroup.closure (S : Set G) := by {
   apply list_prod_mem
   intro x hx
   apply Subgroup.subset_closure
   exact mem_coe_list hx 
}

end ProdList

end Subgroup

import Mathlib.Data.List.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.Set.Basic

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.List.Range

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

@[simp]
def eqSubsetProd (S : A) (g : G):=    ∃ (L : List S),  g = L.gprod 
 
-- #check eqSubsetProd

lemma mem_SubsetProd  (g : S) : eqSubsetProd S ↑g := by {
   use [g]
   norm_num
} 


lemma mem_one_SubsetProd :  eqSubsetProd S 1 := by {
   use []
   norm_num
}

/-
lemma memProd_singleton (x : S) : (x : G) ∈ Subgroup.closure (S : Set G) := by {
   apply Subgroup.subset_closure x.2
}
-/

lemma memProd_singleton : ∀ x :S,  eqSubsetProd S (x : G) := by {
  intro x
  use [x]
  simp 
}


lemma memProd_singleton'  : ∀ x :G, x∈ (S: Set G)  →  eqSubsetProd S (x : G) := by {
  intro x hx
  use [(⟨x, hx⟩:S)]
  simp 
}

lemma memProd_one : eqSubsetProd S (1 : G) := by {
  use []
  simp 
}

lemma memProdSubgroupClosure (L : List S) : L.gprod ∈ Subgroup.closure (S : Set G) := by {
   apply list_prod_mem
   intro x hx
   apply Subgroup.subset_closure
   exact mem_coe_list hx 
}
end ProdList

end Subgroup

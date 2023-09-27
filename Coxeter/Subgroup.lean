import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.List.Range

import Coxeter.List


variable {G : Type _} {A : Type _} [Group G] [SetLike A G] {S : A}

namespace Subgroup
section SubgroupClosure

class  InvMem (S : A): Prop where
   inv_mem: ∀ x:G, x∈ S → x⁻¹ ∈ S 

instance inv_symm [InvMem S] : Inv S := ⟨fun a => ⟨a⁻¹, InvMem.inv_mem a.1 a.2⟩⟩


lemma inv_reverse_coe [InvMem S] (L : List S) :
List.reverse (List.map (fun x => x⁻¹) (L : List G)) =
  Lean.Internal.coeM (List.reverse (List.map (fun x => x⁻¹) L))
  := by {
   induction L with
   | nil => trivial 
   | cons hd tail ih =>
   {
    simp only [coe_cons,List.map_cons,List.reverse_cons,coe_cons,coe_append,ih]
    congr 
  }
}

lemma inv_reverse_inv [InvMem S] (L : List S) : L.gprod ⁻¹ = (List.map (fun x: S => x⁻¹) L).reverse.gprod := by {
   repeat rw [List.gprod]
   rw [List.prod_inv_reverse]
   congr
   exact inv_reverse_coe _ 
}

lemma memInvProdInvClass [InvMem S] (x : G) : eqSubsetProd S x → eqSubsetProd S x⁻¹  := by {
   rintro ⟨L, Lxa, Lxp⟩  
   use (List.map (fun x: S => x⁻¹) L).reverse
   exact inv_reverse_inv L
} 


-- #check Subgroup.closure_induction 

lemma memClosure_if_Prod [InvMem S] {g : G} : g ∈ Subgroup.closure (S : Set G) →  eqSubsetProd S g := by {
   intro hg
   apply @Subgroup.closure_induction G _ (S : Set G) (eqSubsetProd S) g hg 
   .  exact memProd_singleton'
   .  exact memProd_one
   . {
    intro x y hx hy 
    let ⟨Lx, Hx⟩  := hx 
    let ⟨Ly, Hy⟩  := hy 
    use Lx++Ly
    rw [gprod_append,<-Hx,<-Hy]
   } 
   . exact memInvProdInvClass
 }

lemma memClosure_iff_Prod [InvMem S] {g :G} : g ∈ Subgroup.closure S ↔ eqSubsetProd S g:= by 
{
   constructor 
   .  exact memClosure_if_Prod
   . {
      intro ⟨L, HL⟩
      rw [HL]
      exact memProdSubgroupClosure L 
   }
}  


end SubgroupClosure

end Subgroup
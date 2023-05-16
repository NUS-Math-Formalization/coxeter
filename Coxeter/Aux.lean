import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.List.Range

@[simp]
def subsetList {G : Type _} (S : Set G): (Set (List G)) := 
{ L | ∀ a∈ L , a ∈ S}

namespace Subgroup
section SubgroupClosure 
variable {G : Type u3} [Group G] (S : Set G)

lemma cons_hd_subsetList {S : Set G} {hd : G} {tail : List G} (H: hd :: tail ∈ subsetList S) 
: hd ∈ S := H hd (List.mem_cons_self hd tail)


lemma cons_tail_subsetList {S : Set G}{hd : G} {tail : List G} (H: hd :: tail ∈ subsetList S) 
: tail ∈ subsetList S := 
λ a ha =>  H a (List.mem_cons_of_mem hd ha)


@[simp]
def coe_ListG_to_ListS' {S: Set G} (L : List G) (h: L ∈ subsetList S): List S
:= match L with  
| [] => []
| hd ::tail => ⟨hd,by {
      simp at h 
      exact h.1
   } ⟩ :: coe_ListG_to_ListS' tail (by { 
   simp at h
   exact h.2})  




instance {L : List G} (h : L ∈ subsetList S) : CoeDep (L ∈ subsetList S) h (List S) 
:= {
   coe := coe_ListG_to_ListS' L h  
}  

lemma cons_coe_ListG_to_ListS {S : Set G} {hd : G}  {tail : List G} (h : hd :: tail ∈ subsetList S) : coe_ListG_to_ListS' (hd::tail) h =  ⟨hd, cons_hd_subsetList h⟩ :: coe_ListG_to_ListS' tail (cons_tail_subsetList h) := by {
  rfl 
} 


@[simp]
lemma coe_ListS_coe_eq {S : Set G} {L:List G} (h : L∈ subsetList S) :
((h : List S) : List G) = L := by {
 induction L with 
 | nil => {
   rw [Lean.Internal.coeM]
   rfl 
 } 
 | cons hd tail ih => {
      rw [cons_coe_ListG_to_ListS]
      have ihtail := ih ( cons_tail_subsetList h)
      conv =>  
         rhs
         rw [<-ihtail]
 }
}


@[simp]
lemma coe_length_eq {S : Set G} {L: List S} :
L.length = (L : List G).length := by 
{
  induction L with 
  | nil => {rfl} 
  | cons hd tail ih => {
    rw [List.length_cons, ih] 
    rfl 
  }
}  


lemma prod_eq_prod {S : Set G} {L : List G} {h : L ∈ subsetList S} :  ((h : List S): List G).prod  =  L.prod :=  by {
  simp 
} 

lemma cons_in_subsetList {S : Set G} {hd : G} {tail : List G} : hd ∈  S → tail ∈ subsetList S → hd::tail ∈ subsetList S := by {
 intros H1 H2 x hx
 rw [List.mem_cons] at hx
 cases hx with 
 | inl h1 => { rw [h1]
               exact H1} 
 | inr h2 => {
   exact H2 x h2
 }
}   

lemma ListS_is_in_subsetList (S : Set G) (L : List S) : (L : List G) ∈ subsetList S :=
by {
  intro a ha 
  rw [Lean.Internal.coeM] at ha
  simp [List.mem_range] at ha 
  let ⟨a, HSa, hha ⟩ := ha 
  rw [hha.2] 
  exact HSa 
}

@[simp]
lemma nil_in_subsetList {S : Set G} : [] ∈ subsetList S := by {
   rw [subsetList]
   intro a ha 
   exfalso
   exact (List.mem_nil_iff a).1 ha 
} 


lemma coe_in_subsetList {S : Set G} {L:List S}: (L : List G)
∈ subsetList S := by {
  induction L with 
  | nil => { 
     have : Lean.Internal.coeM ([] : List ↑S) = ([] : List G):= by rfl 
     rw [this]
     exact nil_in_subsetList     
  } 
  | cons hd tail ih => {
    have : (Lean.Internal.coeM (hd::tail) : List G)  = (↑ hd) :: (tail : List G) := by rfl
    rw [this]
    exact cons_in_subsetList hd.2 ih 
  }  
}



@[simp]
def eqSubsetProd (S : Set G) : G → Prop := λ (g : G) =>  ∃ (L : List G), (∀ a∈L, a∈ S) ∧ g = L.prod 

lemma mem_SubsetProd (S : Set G) (g : G ): g ∈ S → eqSubsetProd S g := by {
   intro hx 
   use [g]
   constructor 
   { intro a ha
     have : a=g := List.mem_singleton.1 ha 
     rw [this] 
     exact hx
   }
   norm_num
}  

lemma mem_one_SubsetProd (S : Set G) :  eqSubsetProd S 1 := by {
   use []
   norm_num
}

@[simp]
def isInvSymm (S : Set G) := ∀ a ∈ S, a⁻¹ ∈ S 

@[simp] 
def InvSymm (S : Set G) := {a:G | a∈ S ∨ a⁻¹ ∈ S}


lemma mem_InvSymm (S : Set G) : a ∈ S → a ∈ InvSymm S:= Or.inl   

lemma memInv_InvSymm (S : Set G) : a ∈ S → a⁻¹ ∈ InvSymm S:= by {
  rintro ha
  apply Or.inr 
  simp [ha] 
}

lemma memInv_InvSymm' (S : Set G) : a⁻¹ ∈ S → a ∈ InvSymm S:= by {
  rintro ha
  apply Or.inr 
  exact ha 
}
lemma mem_InvSymm_iff (S : Set G) : a ∈ InvSymm S → a⁻¹ ∈ InvSymm S:= by {
   rintro ha 
   cases ha with 
   | inl haa => exact memInv_InvSymm _ haa 
   | inr haa => exact Or.inl haa
}   


lemma eqInvSymm (S : Set G)  (H : isInvSymm S) : S = InvSymm S := by {
   rw [InvSymm]
   ext x
   rw [isInvSymm] at H
   constructor 
   { intro hx 
     simp [hx]}
   {
     intro hx
     apply Or.elim hx 
     simp  
     intro hxx
     have hxx := H x⁻¹ hxx
     simp at hxx
     exact hxx
   }
} 



lemma memClosureInvSymm (S : Set G) : InvSymm S ⊆ Subgroup.closure S:= by 
{
  rw [InvSymm]
  have HH : S ⊆ Subgroup.closure S := Subgroup.subset_closure 
  intro x hx 
  exact hx.elim (fun hxa => HH hxa) (fun hxb => by {
   apply (Subgroup.inv_mem_iff _).1
   exact HH hxb
  }) 
} 

lemma memProdInvSymm (S : Set G) (L : List G) (H : L∈ subsetList (InvSymm S)) : L.prod ∈ Subgroup.closure S := by {
   apply list_prod_mem
   intro x hx
   rw [subsetList] at H
   have := H x hx 
   exact (memClosureInvSymm S this)
} 


lemma memInvProdInvSymm (S : Set G)  (x : G) : eqSubsetProd (InvSymm S) x → eqSubsetProd (InvSymm S) x⁻¹  := by {
   rintro ⟨L, Lxa, Lxp⟩  
   use (List.map (fun x:G => x⁻¹) L).reverse
   apply And.intro
   case left => {
      rintro a ha 
      rw [List.mem_reverse,List.mem_map] at ha
      let ⟨b, hb1, hb2⟩ := ha  
      rw [<-hb2]
      have hb := Lxa b hb1
      exact mem_InvSymm_iff _ hb
   }
   case right => {
      rw [Lxp]
      apply List.prod_inv_reverse
   }
} 

#check Subgroup.closure_induction 

lemma memClosure_if_Prod {g : G} {S : Set G} : g ∈ Subgroup.closure S →  eqSubsetProd (InvSymm S) g := by {
   intro hg
   apply @Subgroup.closure_induction _ _ S (eqSubsetProd (InvSymm S)) g hg 
   {
     intro x hx
     have hxx := mem_InvSymm S hx
     apply mem_SubsetProd _ _ hxx
   } 
   {
     apply mem_one_SubsetProd 
   }
   { 
      intro x y hx hy  
      let ⟨Lx, Hx⟩  := hx 
      let ⟨Ly, Hy⟩  := hy 
      use Lx++Ly
      constructor 
      {
         intro a ha 
         rw [List.mem_append] at ha
         cases ha with 
         | inl La => exact Hx.1 a La
         | inr La => exact Hy.1 a La 
      }
      {rw [Hx.2,Hy.2,List.prod_append] }
   }
   {
     intro x
     apply memInvProdInvSymm 
   }
}

lemma memClosure_iff_Prod {g : G} {S : Set G} : g ∈ Subgroup.closure S ↔ eqSubsetProd (InvSymm S) g:= by 
{
   constructor 
   .  exact memClosure_if_Prod
   . {
    rw [eqSubsetProd, ] 
    intro ⟨L, HLa, HLb⟩ 
    rw [HLb] 
    apply memProdInvSymm _ _ HLa
   }
}  


end SubgroupClosure

end Subgroup

import Mathlib.Data.SetLike.Basic


import Coxeter.Basic


variable {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S] {J:Set S}

#check Set.Elem
#check Subtype.coe_image_subset
#check Subgroup.subtype

instance : SetLike (Set S) G where
  coe := fun J : Set S => Subtype.val '' J
  coe_injective':=by {simp;intro a b;exact Subtype.val_inj.1}


lemma mem_coe_coe (j : J) : ((j: S): G) ∈ (J : Set G) := by {
  rw [Lean.Internal.coeM]
  simp only [Set.pure_def, Set.bind_def]
  rw [Set.mem_iUnion]
  use ⟨j,(by simp only [Subtype.coe_prop])⟩  
  simp only [Subtype.coe_eta, Subtype.coe_prop, Set.iUnion_true, Set.mem_singleton_iff,Subtype.val]
  rfl
}

def subset_to_set {S:Set G} : Set S → Set G:= fun J:Set S => Subtype.val '' J

def ParabolicSubgroup {G : Type u_1} [Group G] {S : outParam (Set G)} (J: Set S):= Subgroup.closure (J : Set G)

#check Subgroup.subset_closure


def coe_set_to_subset_of_inclusion (J:Set G) (H: Set G) (hsub: J ⊆ H):= Set.image (Set.inclusion hsub) Set.univ


def GenofParabolicSubgroup := coe_set_to_subset_of_inclusion (J : Set G) ((ParabolicSubgroup J):Set G) (@Subgroup.subset_closure G _ (J : Set G))


def coeJ_mk (J : Set S) : J → ParabolicSubgroup J := fun j => ⟨j, (
  by {
    rw [ParabolicSubgroup]
    apply Subgroup.subset_closure
    exact mem_coe_coe j
  }
)⟩  

def coeSetJ (JJ : Set J) := coeJ_mk J '' JJ

instance : SetLike (Set J) (ParabolicSubgroup J) where
  coe := coeSetJ 
  coe_injective' := sorry

instance : @orderTwoGen (ParabolicSubgroup J) _ (@Set.univ J) where
order_two := by {
  intro x hx
  have hxsub: ↑x ∈ S:=sorry
  have aux:= @orderTwoGen.order_two G _ S _ ↑x hxsub
  rw [←Subgroup.coe_mul,←Subgroup.coe_one] at aux
  constructor
  {
    apply Subtype.coe_inj.1 
    exact aux.1
  }
  simp at *
  exact aux.2
}
expression := sorry

instance : @CoxeterSystem (ParabolicSubgroup J) (@Set.univ J) _ _ where
exchange :=sorry
deletion :=sorry


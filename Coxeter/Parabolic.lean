import Mathlib.Data.SetLike.Basic


import Coxeter.Basic


variable {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S] {J:Set S}

#check Set.Elem
#check Subtype.coe_image_subset
#check Subgroup.subtype

instance : SetLike (Set S) G where
  coe := fun J:Set S => Subtype.val '' J
  coe_injective':=by {simp;intro a b;exact Subtype.val_inj.1}

def subset_to_set {S:Set G} : Set S → Set G:= fun J:Set S => Subtype.val '' J

def ParabolicSubgroup  (J: Set S):= Subgroup.closure (SetLike.coe J)
#check Subgroup.subset_closure


def coe_set_to_subset_of_inclusion (J:Set G) (H: Set G) (hsub: J ⊆ H):= Set.image (Set.inclusion hsub) Set.univ


def GenofParabolicSubgroup := coe_set_to_subset_of_inclusion (SetLike.coe J) ((ParabolicSubgroup J):Set G) (@Subgroup.subset_closure G _ (SetLike.coe J))

instance : SetLike (Set S) (Subgroup G) where
  coe:= fun J => by {exact coe_set_to_subset_of_inclusion (SetLike.coe J) ((ParabolicSubgroup J):Set G) (@Subgroup.subset_closure G _ (SetLike.coe J))}



instance : @orderTwoGen (ParabolicSubgroup J) (sorry) GenofParabolicSubgroup :=sorry
#check Set.inclusion
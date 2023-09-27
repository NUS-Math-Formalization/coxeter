import Coxeter.Basic


variable {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S]


local notation :max "ℓ(" g ")" => (@length G  _ S _ g)




def ltone (u w: G) := ∃ t: T S, w = u * t ∧ ℓ(u) < ℓ(w)


def lt (u w:G):= ∃ L:List G, List.Forall₂ (@ltone G _ S _) (u::L) (L++[w])

def le (u w:G):= u=w ∨ @lt G _ S _ u w

instance Bruhat.LT : LT G where
  lt:=@lt G _ S _

instance Bruhat.LE : LE G where
  le:=@le G _ S _

variable (u v:G)
#check u≤v

instance Bruhat.poset : PartialOrder G where
le := @le G _ S _
lt := @lt G _ S _
le_refl  := fun x => Or.inl (refl x)
le_trans := fun (x y z:G) => by{ 
  intros lxy lyz 
  sorry
}
lt_iff_le_not_le  := sorry
le_antisymm:= fun (x y:G) => sorry

lemma ltone_is_lt {u w:G}  : ltone u w → u < w := by{
  intro H
  use []
  simp
  assumption
}


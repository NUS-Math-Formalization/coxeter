import Coxeter.Basic

import Mathlib.Data.Set.Card


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

def BruhatInte (x y : G) : Set G := {a | x ≤ a ∧ a ≤ y } 

#check Set.ncard
#check length



lemma SubwordAux (L L':List S) (hred:reduced_word L) (hw: (w:G) = L.gprod) (hsub: List.Sublist L' L) (hu: u = L'.gprod): ∃ (v: G) (L'':List S), u < v ∧ ℓ(v) = ℓ(u) + 1 ∧ v = L''.gprod:=by
  sorry

theorem SubwordProp (L: List S) (u w : G) (hred:reduced_word L) (hw: (w:G) = L.gprod) : u ≤ w ↔ ∃ (L': List S), reduced_word L' ∧ List.Sublist L' L ∧ u = L'.gprod where
  mp := by
    sorry 
  mpr := fun
    | .intro w h => by
      sorry

lemma BruhuatInteIsFin (u w :G)  : Set.ncard (@BruhatInte G  _  S _ u w) ≤ 2^ℓ(w):=sorry

lemma leIffInvle (u w : G) :  u ≤ w ↔ u⁻¹ ≤ w⁻¹ := sorry

theorem ChainProp (u w :G) (hlt: u < w) : ∃ (L: List G) (h:L ≠ [])(n:Fin L.length), u = L.head h∧ w =L.ilast' w ∧ ℓ(L.get n) = ℓ(u) + n:= sorry

def OrderCovering (u w:G) := u < w ∧ ℓ(u) + 1 = ℓ(w) 

local notation lhs:65 " ◁  " rhs:65 => (@OrderCovering G  _ S _ _ lhs rhs)

lemma LiftingProp (u w : G) (h:s∈ D_L w) : u ≤ s*w ∧ s*u ≤ w := sorry

class DirectedPoset (α:Type u) extends PartialOrder α where 
directed:∀ (u w:α) , ∃ z:α, u ≤ z ∧ w ≤ z


lemma BruhatOrderIsDir :DirectedPoset G:=sorry

lemma Bruhat'Congr' (x y :G) (t:T S) (hlt: x < x*t) (hlt: y < (t:G)*y) : x * y < x * t * y :=by
  let t' :=x * t * x⁻¹
  have hc :x*t*y = t'*x*y := by simp
  by_contra hf
  sorry
  -- have hredx := @reduced_word_exist G A _ _ S _ x
  -- have hredy := @reduced_word_exist G A _ _ S _ y
  -- --have hf' := @le_of_not_lt G _ (x * t * y) (x * y) hf
  -- let ⟨L1,hL1⟩ := hredx 
  -- let ⟨L2,hL2⟩ := hredy


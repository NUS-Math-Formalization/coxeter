import Coxeter.CoxeterSystem

import Mathlib.Data.Set.Card

section SimpleReflections

@[ext]
class SimpleRefl (G: Type*) [Group G] where
  carrier : Set G
  order_two :  ∀ (x:G) , x ∈ carrier →  x * x = (1 :G) ∧  x ≠ (1 :G)
  expression : ∀ (x:G) , ∃ (L : List carrier),  x = L.gprod



instance SimpleRefl.setlike [Group G]: SetLike (SimpleRefl G) G where
  coe := fun S => S.carrier
  coe_injective' p q h:= by
    cases p
    cases q
    congr


@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl

end SimpleReflections

class CoxeterGroup (G: Type*) extends Group G where
  S : Set G
  hS : CoxeterSystem S

namespace CoxterGroup

variable {G:Type*} [CoxeterGroup G]

def T [S: SimpleRefl G] : Set G:= {x:G| ∃ (w:G)(s : h.S) , x = w*s*w⁻¹}

variable {G : Type*} [Group G] {S :Set G} [hS:OrderTwoGen S]

local notation :max "ℓ(" g ")" => (OrderTwoGen.length S g)


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
local notation :max "ℓ(" g ")" => (OrderTwoGen.length S g)


local notation : max "TT" => (@T G _ S)

-- The adjacent relation in the Bruhat Order
-- u < w if ∃ t ∈ T such that w = u * t ∧  ℓ(u) < ℓ(w)
def Bruhat.lt_adj (u w:G) := ∃ t ∈ TT  , w = u * t ∧ ℓ(u) < ℓ(w)

def Bruhat.lt (u w:G):= Relation.TransGen (Bruhat.lt_adj S) u w

def Bruhat.le (u w:G):= Relation.ReflTransGen (Bruhat.lt_adj S) u w


instance Bruhat.LT : LT G where
  lt := Relation.TransGen (Bruhat.lt_adj S)

instance Bruhat.LE : LE G where
  le:= Relation.TransGen (@Bruhat.lt_adj G _ S _)


--  @le G _ S _


instance Bruhat.poset : Preorder G where
  le := Relation.ReflTransGen (@Bruhat.lt_adj G _ S _)
  lt :=
  le_refl  := by intro _; simp [Relation.ReflTransGen.refl]
  le_trans := fun _ _ _ => Relation.ReflTransGen.trans


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
    intro hle
    exact Or.elim hle (fun h1 =>(by rw [h1];use L)) (fun h1=>(by{
      rcases h1 with ⟨Laux,h2⟩
      induction' Laux with head tail tail_ih
      case nil => simp [ltone]at h2;sorry
      case cons =>sorry
    }))

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

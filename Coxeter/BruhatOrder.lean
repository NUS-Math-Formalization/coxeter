import Coxeter.CoxeterSystem

import Mathlib.Data.Set.Card

section SimpleReflections
open OrderTwoGen

class HOrderTwoGenGroup (G: Type*) extends Group G where
  S: Set G
  order_two :  ∀ (x:G) , x ∈ S →  x * x = (1 :G) ∧  x ≠ (1 :G)
  expression : ∀ (x:G) , ∃ (L : List S),  x = L.gprod

namespace HOrderTwoGenGroup
variable (G :Type*) [hG: HOrderTwoGenGroup G]
variable {H :Type*} [hH: HOrderTwoGenGroup H]

@[simp]
def SimpleRefls := hG.S

#check SimpleRefls G

instance SimpleRefls.toOrderTwoGen  : @OrderTwoGen H _ (SimpleRefls H) where
  order_two := hH.order_two
  expression := hH.expression


instance SimpleRefls.toOrderTwoGen'  : @OrderTwoGen H _ (hH.S) where
  order_two := hH.order_two
  expression := hH.expression

noncomputable def length  (g :H) := OrderTwoGen.length (hH.S) g

notation:100 "ℓ(" g:101 ")" => (length g)

end HOrderTwoGenGroup

class CoxeterGroup (G:Type*) extends HOrderTwoGenGroup G where
  exchange : ∀ (L:List S) (s: S), reduced_word L →
      (length S (s * L)) ≤ (length S (L)) → ∃ (i: Fin L.length), (s :G) * L= (L.removeNth i)
  exchange' : ∀ (L:List S) (s: S), reduced_word L →
      (length S (L * s)) ≤ (length S (L)) → ∃ (i: Fin L.length), L * (s:G)= (L.removeNth i)
  deletion: ∀ (L:List S), (length S L) < L.length → ∃ (j: Fin L.length), ∃ (i:Fin j), (L:G)= ((L.removeNth j).removeNth i)

namespace CoxeterGroup
open HOrderTwoGenGroup

instance SimpleRefl_isCoxeterSystem  {G:Type*} [hG:CoxeterGroup G]: @CoxeterSystem G _ (hG.S) where
  exchange := hG.exchange
  exchange' := hG.exchange'
  deletion := hG.deletion


def Refls (G:Type*) [CoxeterGroup G]: Set G:= {x:G| ∃ (w:G)(s : SimpleRefls G) , x = w*s*w⁻¹}

namespace Bruhat
variable {G:Type*} [CoxeterGroup G]

@[simp]
abbrev lt_adj  (u w:G) := ∃ t ∈ Refls G, w = u * t ∧ ℓ(u) < ℓ(w)

@[simp]
abbrev lt_adj'  (u w:G) := ∃ t ∈ Refls G, w = t * u  ∧ ℓ(u) < ℓ(w)


lemma lt_adj_iff_lt_adj' {u w:G} : lt_adj u v ↔ lt_adj' u v := by sorry


abbrev lt  (u w:G):= Relation.TransGen (Bruhat.lt_adj) u w

abbrev le (u w:G):= Relation.ReflTransGen (Bruhat.lt_adj) u w

/-
instance Bruhat.LT {G:Type*} [CoxeterGroup G] : LT G where
  lt := lt

instance Bruhat.LE {G:Type*} [CoxeterGroup G] : LE G where
  le:= le
 -/


lemma lenght_le_of_le  {u w :G} : le u w → ℓ(u) ≤ ℓ(w) := by sorry


lemma lenght_lt_of_lt  {u w :G} : lt u w → ℓ(u) < ℓ(w) := by sorry

lemma lt_of_le_of_lenght_lt  {u w :G} : le u w → ℓ(u) < ℓ(w) → lt u w:= by sorry


lemma eq_of_le_of_lenght_ge  {u w :G} : le u w → ℓ(u) ≥  ℓ(w) → u = w := by sorry


instance particalorder: PartialOrder G where
le := le
lt := lt
le_refl  := by intro _; simp [Relation.ReflTransGen.refl]
le_trans := fun _ _ _ => Relation.ReflTransGen.trans
lt_iff_le_not_le  := by
    -- use length_le_of_le to prove -> direction
    -- use lt_of_le_of_length_lt and eq_of_le_of_lenght_ge
    sorry
le_antisymm:= fun (x y:G) => by sorry



def Interval (x y : G) : Set G := Set.Icc x y

-- Formulate the theorem on subword property

-- Show that Bruhat interval is finite

instance Interval.fintype {x y : G} : Fintype (Interval x y) where
  elems := by sorry
  complete := by sorry

end Bruhat

end CoxeterGroup


/-



lemma ltone_is_lt {u w:G}  : ltone u w → u < w := by{
  intro H
  use []
  simp
  assumption
}


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
-/

section test
variable (G:Type*) [hG:CoxeterGroup G]

variable  (g:G)

#check ℓ(g)

variable (u v:G)
#check u < v

end test

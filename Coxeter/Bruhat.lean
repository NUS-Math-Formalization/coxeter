import Coxeter.Defn
import Coxeter.Length
import Std.Data.List.Basic
import Mathlib.Data.Set.Card




open CoxeterSystem
variable {G : Type _} {A : Type _} [Group G] [SetLike A G] {S : A} [CoxeterSystem S]
variable [orderTwoGen S]


instance Bruhat.LT : LT G where 
lt:= @ltB G A _ _ S _

instance Bruhat.LE : LE G where 
le:= @leB G A _ _ S _

lemma leBIsRefl (x:G) :  x ≤ x := sorry
#check leB
instance leB.IsRefl  : IsRefl G (· ≤ ·)  := ⟨fun x => Or.inl (refl x)⟩

lemma leBtrans (x y z:G) :  x ≤ y →  y ≤ z → x ≤ z:=sorry
--lemma leBtrans (x y z:G) : x ≤B y → y ≤B z → x ≤B z := sorry  

instance leB.IsTrans : IsTrans G (· ≤ ·) := ⟨fun (x y z:G) => leBtrans x y z⟩

lemma leBAntisymm (x y : G) : x ≤ y → y ≤ x → x = y:=sorry

instance leB.IsAntisymm : IsAntisymm G (· ≤ ·) := ⟨fun (x y:G) => leBAntisymm x y⟩


instance Bruhat.PartialOrder: PartialOrder G where 
le := @leB G A _ _ S _
lt := @ltB G A _ _ S _ 
le_refl  := fun x => Or.inl (refl x)
le_trans := fun (x y z:G) => leBtrans x y z
lt_iff_le_not_le  := sorry
le_antisymm:= fun (x y:G) => leBAntisymm x y

def BruhatInte (x y : G) (h: x ≤ y): Set G := {a | x ≤ a ∧ a ≤ y } 

#check Set.ncard
#check length

local notation:max "ℓ(" g ")" => (@length G A _ _ S _ g)   
local notation "TT" => (@T G A _ _ S)
--local notation just in  current file?? 


lemma SubwordAux (L L':List S) (hred:reduced_word L) (hw: (w:G) = L.gprod) (hsub: List.Sublist L' L) (hu: u = L'.gprod): ∃ (v: G) (L'':List S), u < v ∧ ℓ(v) = ℓ(u) + 1 ∧ v = L''.gprod:=by
  done

theorem SubwordProp (L: List S) (u w : G) (hred:reduced_word L) (hw: (w:G) = L.gprod) : u ≤ w ↔ ∃ (L': List S), reduced_word L' ∧ List.Sublist L' L ∧ u = L'.gprod where
  mp := by
    done
  mpr := fun
    | .intro w h => by
      done

lemma BruhuatInteIsFin (u w :G) (h:u ≤ w) : Set.ncard (BruhatInte u w h) ≤ 2^ℓ(w):=sorry

lemma leIffInvle (u w : G) : @leB G A _ _ S _ u w ↔ @leB G A _ _ S _ u⁻¹ w⁻¹ := sorry

theorem ChainProp (u w :G) (hlt: u < w) : ∃ (L: List G) (h:L ≠ [])(n:Fin L.length), u = L.head h∧ w =L.ilast' w ∧ ℓ(L.get n) = ℓ(u) + n:= sorry

def OrderCovering (u w:G) := u < w ∧ ℓ(u) + 1 = ℓ(w) 

local notation lhs:65 " ◁  " rhs:65 => (@OrderCovering G A _ _ S _ _ lhs rhs)

lemma LiftingProp (u w : G) (h:s∈ D_L w) : u ≤ s*w ∧ s*u ≤ w := sorry

class DirectedPoset (α:Type u) extends PartialOrder α where 
directed:∀ (u w:α) , ∃ z:α, u ≤ z ∧ w ≤ z


lemma BruhatOrderIsDir :DirectedPoset G:=sorry

lemma Bruhat'Congr' (x y :G) (ht:t∈TT) (hlt: x < x*t) (hlt: y < (t:G)*y) : x * y < x * t * y :=by
  let t' :=x * t * x⁻¹
  have hc :x*t*y = t'*x*y := by simp
  by_contra hf
  have hredx := @reduced_word_exist G A _ _ S _ x
  have hredy := @reduced_word_exist G A _ _ S _ y
  --have hf' := @le_of_not_lt G _ (x * t * y) (x * y) hf
  rcases hredx with ⟨L1| ⟨hx1,hx2⟩⟩
  sorry
  sorry






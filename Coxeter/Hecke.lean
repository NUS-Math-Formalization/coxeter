import Coxeter.Basic
import Coxeter.Bruhat
import Coxeter.Rpoly

import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Reverse
import Mathlib.Data.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Polynomial.Laurent
import Mathlib.Algebra.DirectSum.Basic

variable {G :(Type _)} [Group G] {S : (Set G)} [orderTwoGen S] [CoxeterSystem G S]
local notation :max "ℓ(" g ")" => (@length G  _ S _ g)
open Classical



section Hecke_algebra

def Hecke (G:Type _):= DirectSum G (fun _ => LaurentPolynomial ℤ)

--def Hecke (G:Type _):= Π₀ (i:G), (fun _ => LaurentPolynomial ℤ) i

noncomputable instance Hecke.AddCommMonoid : AddCommMonoid (Hecke G):= instAddCommMonoidDirectSum G _

noncomputable instance Hecke.Module : Module (LaurentPolynomial ℤ) (Hecke G):= DFinsupp.module

noncomputable instance Hecke.Module.Free : Module.Free (LaurentPolynomial ℤ) (Hecke G):= Module.Free.directSum _ _

noncomputable instance Hecke.Sub : Sub (Hecke G) := DFinsupp.instSubDFinsuppToZeroToNegZeroClassToSubNegZeroMonoidToSubtractionMonoid
--Dfinsupp.funlike
instance Hecke.funLike : FunLike (Hecke G) G (fun _ => LaurentPolynomial ℤ):= instFunLikeDirectSum _ _


noncomputable def TT : G → Hecke G:= fun w => DFinsupp.single w 1

--Ts *Tw = Ts*Ts*Tu= (q-1)Ts*Tu+qTu=(q-1) Tw + qT(s*w) if s∈D_L w
noncomputable def q :=@LaurentPolynomial.T ℤ _ 1
noncomputable def qinv :=@LaurentPolynomial.T ℤ _ (-1)

local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)

--DFinsupp.single w (q-1) + DFinsupp.single (s*w) q))
noncomputable def mulsw (s:S) (w:G)  : Hecke G :=
  if s.val ∈ D_L w then
  ((q-1) • TT w + q • TT (s*w))
  else TT (s*w)

--Ts* ∑ᶠ w, h (w) * TT w = ∑ᶠ h w * Ts * T w
noncomputable def muls (s:S) (h:Hecke G) : Hecke G:=
finsum (fun w:G =>  (h w) • (mulsw s w) )
--∑ᶠ (w :G), ((h w) • (mulsw s w):Hecke G)

def llr (u v:G) := ℓ(u) < ℓ(v) ∧ ∃ s∈S , s*u=v

theorem well_founded_llr : WellFounded (@llr G _ S _ ) :=by{
  apply WellFounded.intro
  intro x
  apply Acc.intro

}

noncomputable def mulw.F (u :G) (F:(w:G) → llr w u → Hecke G → Hecke G) (v:Hecke G): Hecke G:=
if h:u =1 then v
  else(
    let s:= Classical.choice (nonemptyD_R u h)
    have :s.val ∈ S:= Set.mem_of_mem_of_subset s.2 (Set.inter_subset_right _ S)
    @muls G _ S _ ⟨s,this⟩ (F (s.val*u) (sorry) v)
  )

noncomputable def mulw :G → Hecke G → Hecke G := @WellFounded.fix G (fun _ => Hecke G → Hecke G) llr well_founded_llr mulw.F

noncomputable def HeckeMul (h1:Hecke G) (h2:Hecke G) : Hecke G :=
finsum (fun w:G => (h1 w) • mulw w h2)

noncomputable def Hecke_inv_s (s:S) := q⁻¹ • (TT s.val) - (1-q⁻¹) • (TT 1)

noncomputable def Hecke_invG.F (u:G) (F: (w:G) → llr w u → Hecke G): Hecke G:= if h:u=1 then TT 1
else (
   let s:= Classical.choice (nonemptyD_R u h)
   HeckeMul (F (s*u) (sorry)) (Hecke_inv_s s)
  )

noncomputable def Hecke_invG : G → Hecke G := @WellFounded.fix G (fun _ => Hecke G) llr well_founded_llr Hecke_invG.F

local notation : max "(TT" w ")⁻¹" => Hecke_invG w

noncomputable instance LaurentPolynomial.CommSemiring : CommSemiring (LaurentPolynomial ℤ):=
AddMonoidAlgebra.commSemiring

instance Hecke.Semiring : Semiring (Hecke G) :=sorry

instance Hecke.algebra : Algebra (LaurentPolynomial ℤ) (Hecke G):=
Algebra.ofModule (sorry) (sorry)


lemma mul_le_of_lt_of_mul_lt (s:S) (w:G) (h: s*w < w) : x < w → s*w ≤ w:=by {
  intro h1
  if (s*x < x) then {sorry}
  else {sorry}
}

def length_le (w:G) := {x:G| ℓ(x) ≤ ℓ(w)}

variable {R:@Rpoly G _ S _}

theorem Hecke_inverse (w:G) : (TT w)⁻¹ = ((-1)^ℓ(w) * (q⁻¹)^ℓ(w)) • finsum (fun (x: length_le w) => (Polynomial.toLaurent ((-1)^ℓ(x)*(R.R x w))) • TT x.val):=sorry

end Hecke_algebra

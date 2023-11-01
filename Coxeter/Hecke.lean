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

noncomputable instance Hecke.AddCommMonoid : AddCommMonoid (Hecke G):= instAddCommMonoidDirectSum G _

noncomputable instance Hecke.Module : Module (LaurentPolynomial ℤ) (Hecke G):= DirectSum.instModuleDirectSumInstAddCommMonoidDirectSum

noncomputable instance Hecke.Module.Free : Module.Free (LaurentPolynomial ℤ) (Hecke G):= Module.Free.directSum _ _

instance Hecke.funLike : FunLike (Hecke G) G (fun _ => LaurentPolynomial ℤ):=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ ↦ fun (h : f₁ = f₂) ↦ by
    subst h
    congr
    apply Subsingleton.elim ⟩

/-- Helper instance for when there are too many metavariables to apply `FunLike.coeFunForall`
-- directly. -/
-- instance : CoeFun (Hecke G) (fun _ => LaurentPolynomial ℤ) := sorry

noncomputable def TT : G → Hecke G:= fun w => DFinsupp.single w 1

def llr (u v:G) := ℓ(u) < ℓ(v) ∧ ∃ s∈S , s*u=v

theorem well_founded_llr : WellFounded (@llr G _ S _ ) :=sorry


-- def HeckeMul_aux.F (v:G) (F:(w:G) → llr w v → S → H) (u:S): H:=
-- if hv:v=1 then TT u else
-- (
-- --   if ℓ(u*v)<ℓ(v) then (@LaurentPolynomial.T ℤ _ 1 - LaurentPolynomial.T 0) • (F (u*v) (sorry) u) + (@LaurentPolynomial.T ℤ _ 1) • TT (u*v) else (TT u*v)
-- -- )

-- noncomputable def HeckMul_aux : G → S → H:= @WellFounded.fix G (fun g => S → H) llr well_founded_llr HeckeMul_aux.F

--Ts *Tw = Ts*Ts*Tu= (q-1)Ts*Tu+qTu=(q-1) Tw + qT(s*w) if s∈D_L w
noncomputable def q :=@LaurentPolynomial.T ℤ _ 1

variable (h:Hecke G)(w:G)
#check h w

noncomputable def mulsw (s:S) (w:G)  : Hecke G :=
  if s.val ∈ D_L w then
  (DFinsupp.single w (q-1) + DFinsupp.single (s*w) q)
  else(
    TT (s*w)
  )
--Ts* ∑ᶠ w, h (w) * TT w = ∑ᶠ h w * Ts * T w
noncomputable def muls (s:S) (h:Hecke G) : Hecke G:=
finsum (fun w:G =>  (h w) • (mulsw s w) )
--∑ᶠ (w :G), ((h w) • (mulsw s w):Hecke G)

noncomputable def HeckeMul.F (u :G) (F:(w:G) → llr w u → G → Hecke G) (v:G): Hecke G:=
if h:u =1 then TT v else
  (
        let s:= Classical.choice (nonemptyD_R u h)
        mulsw s
      )



noncomputable def HeckeMul :G → G →H := @WellFounded.fix G (fun g => G → H) llr well_founded_llr HeckeMul.F

end Hecke_algebra

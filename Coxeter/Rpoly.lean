import Coxeter.Basic
import Coxeter.Bruhat

import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Reverse
import Mathlib.Data.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Polynomial.Laurent

variable {G :(Type _)} [Group G] {S : (Set G)} [orderTwoGen S] [CoxeterSystem G S]  
local notation :max "ℓ(" g ")" => (@length G  _ S _ g)
open Classical
-- class Rploy (u v:G)  (R_poly : Polynomial ℤ) where
--   not_le: ¬ (u ≤ v) → R_ploy = 0
--   eq: u = v → R_ploy = 1
--   sMemD_Ru: ∀ s ∈ D_R v, s∈D_R u → R_ploy = R

structure Rpoly where 
  R: G → G → Polynomial ℤ
  not_le:∀(u v:G), ¬ (u ≤ v) → R u v = 0
  eq:∀(u v:G), u = v → R u v = 1
  sMemD_Ru: ∀(u v:G),s ∈ D_R v → s ∈ D_R u → R u v = R (u*s) (v*s)
  sNotMemD_Ru: ∀(u v:G),s ∈ D_R v → s ∉ D_R u → R u v = X*R (u*s) (v*s) + (X-1) * R u (v*s)

#check Rpoly




variable {R:@Rpoly G _ S _}
lemma monic_R_poly (u v: G) (h: u ≤ v) (R:@Rpoly G _ S _): Polynomial.Monic (R.R u v) ∧ Polynomial.degree (R.R u v)  = ℓ(v)-ℓ(u) ∧ Polynomial.constantCoeff (R.R u v) = (-1)^(ℓ(v)-ℓ(u)):=sorry

structure KLpoly where
P: G → G → Polynomial ℤ
not_le:∀(u v:G), ¬ (u ≤ v) → P u v = 0
eq:∀(u v:G), u = v → P u v = 1
deg_le_of_lt: ∀(u v:G), u < v → Polynomial.degree (P u v) ≤ ((ℓ(v)-ℓ(u)-1)/2:ℕ)
le:∀(u v:G), u ≤ v → X^(ℓ(v)-ℓ(u))* Polynomial.reverse (P u v) = (Finset.sum (BruhatInte u v) (fun a => R.R u a * P a v))* X^(Polynomial.natDegree (P u v))


lemma constant_eq_one_of_KL (u v :G) (h : u ≤ v) (KL:@KLpoly G _ S _ R): Polynomial.constantCoeff (KL.P u v) = 1:=sorry

def rr  (y x :G) := ∃ s∈D_R x, y*s = x

def rrv (v:G) (y x :{ z:G// z ≤ v}):= ∃ s,s∉ D_R (x:G)∧ y = (x:G)*s

theorem well_founded_rrv : WellFounded (@rrv G _ S _ v) :=sorry
theorem well_founded_rr : WellFounded (@rr G _ S _) := sorry

-- def Rv.F (v:G) (u:{ z:G// z ≤ v}) (F:(x : { z:G// z ≤ v}) → ((y : { z:G// z ≤ v}) → rrv v y x → Polynomial ℤ) → Polynomial ℤ) : Polynomial ℤ := if H:u=v then 1 else {
--   sorry
-- }

-- def Rv (v:G) :fun (u:{ z:G// z ≤ v}) => Polynomial ℤ:= WellFounded.Fix well_founded_rrv Rv.F

lemma nonemptyD_R(v:G) (h:v ≠ 1) :Nonempty (D_R v):=sorry

noncomputable def RF  (v:G) (F: (y : G) → rr y v → (G→ Polynomial ℤ)) : G → Polynomial ℤ:=
 if hv:v=1 then
 (fun u:G =>if u=1 then 1 else 0)
 else (
  let s:= Classical.choice (nonemptyD_R v hv)
  fun u => if v < u then 0 else (
    if v = u then 1 else (
      if s.val ∈D_R u then (
        F (v*(s.val)) (sorry) (u*(s.val)) 
      
      )
      else(
         --(F (u*s) (sorry) (v*s) ) *Polynomial.X + (Polynomial.X-1) * (F u (sorry) (v*s))
        (F (v*s) (sorry) (u*s) ) *Polynomial.X + (Polynomial.X-1) * (F (v*s) (sorry) u)
      )
    )
  )
 )

noncomputable def defaultR := @WellFounded.fix G (fun g => G → Polynomial ℤ) rr (well_founded_rr) (RF)

instance : Unique (@Rpoly G _ S _) where
  default:= @defaultR G _ S _
  uniq :=sorry

#check defaultR

variable [AddCommMonoid H][Module (LaurentPolynomial ℤ) H] [Semiring H]

-- structure generic_algebra where
-- FreeModule: Module.Free A ε
-- algebra: Algebra A ε
-- a: G → A
-- b: G → A
-- T: G → ε
-- mul1: ∀ (s w :G), s∈S → ℓ(w) < ℓ(s*w) → T s * T w = T (s*w)
-- mul2: ∀ (s w :G), s∈S → ℓ(s*w) < ℓ(w) → T s * T w = a s • T w + b s • T (s*w)

-- structure Hecke_algebra where
-- FreeModule: Module.Free (LaurentPolynomial ℤ) H
-- algebra: Algebra (LaurentPolynomial ℤ) H
-- TT: G → H
-- mul1: ∀ (s w :G), s∈S → ℓ(w) < ℓ(s*w) → TT s * TT w = TT (s*w)
-- mul2: ∀ (s w :G), s∈S → ℓ(s*w) < ℓ(w) → TT s * TT w = (@LaurentPolynomial.T ℤ _ 1 - LaurentPolynomial.T 0) • TT w + (@LaurentPolynomial.T ℤ _ 1) • TT (s*w)

section Hecke_algebra

def Hecke (G:Type _):= G → LaurentPolynomial ℤ

noncomputable instance Hecke.AddCommMonoid : AddCommMonoid (Hecke G):= Pi.addCommMonoid

instance Hecke.Module : Module (LaurentPolynomial ℤ) (Hecke G):=_

instance Hecke.FreeModule : Module.Free (LaurentPolynomial ℤ) (Hecke G) where
exists_basis := Pi.basis

instance Hecke.HSMul :HSMul (LaurentPolynomial ℤ) (Hecke G) (Hecke G) := _

noncomputable def TT : G → Hecke G:= fun w => Pi.single w 1

def llr (u v:G) := ℓ(u) < ℓ(v) ∧ ∃ s∈S , s*u=v

theorem well_founded_llr : WellFounded (@llr G _ S _ ) :=sorry

#check Module.smul

-- def HeckeMul_aux.F (v:G) (F:(w:G) → llr w v → S → H) (u:S): H:=
-- if hv:v=1 then TT u else 
-- (
-- --   if ℓ(u*v)<ℓ(v) then (@LaurentPolynomial.T ℤ _ 1 - LaurentPolynomial.T 0) • (F (u*v) (sorry) u) + (@LaurentPolynomial.T ℤ _ 1) • TT (u*v) else (TT u*v)
-- -- )

-- noncomputable def HeckMul_aux : G → S → H:= @WellFounded.fix G (fun g => S → H) llr well_founded_llr HeckeMul_aux.F

--Ts *Tw = Ts*Ts*Tu= (q-1)Ts*Tu+qTu=(q-1) Tw + qT(s*w) if s∈D_L w
noncomputable def q :=@LaurentPolynomial.T ℤ _ 1

noncomputable def mulsw (s:S) (w:G)  : Hecke G := 
  if s.val ∈ D_L w then 
  (Pi.single w q-1 + Pi.single (s*w) q)
  else(
    TT (s*w)
  )
--Ts* ∑ᶠ w, h (w) * TT w = ∑ᶠ h w * Ts * T w
noncomputable def muls (s:S) (h:Hecke G) : Hecke G:= 
finsum (fun w:G => Module.smul (h w) (mulsw s w) ) 
--∑ᶠ (w :G), ((h w) • (mulsw s w):Hecke G)

noncomputable def HeckeMul.F (u :G) (F:(w:G) → llr w u → G → Hecke G) (v:G): Hecke G:=
if h:u =1 then TT v else 
  (
      
        let s:= Classical.choice (nonemptyD_R u h)
        mulsw s 
      )
      
  )

noncomputable def HeckeMul :G → G →H := @WellFounded.fix G (fun g => G → H) llr well_founded_llr HeckeMul.F

end Hecke_algebra
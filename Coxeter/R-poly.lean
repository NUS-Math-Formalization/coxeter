import Coxeter.Basic
import Coxeter.Bruhat

import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Reverse
import Mathlib.Data.Polynomial.Basic

variable {G :(Type _)} [Group G] {S : (Set G)} [orderTwoGen S] [CoxeterSystem G S]  
local notation :max "ℓ(" g ")" => (@length G  _ S _ g)

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
instance : Unique (@Rpoly G _ S _) where
  default:=sorry
  uniq :=sorry

-- def Rpoly : G → G → Polynomial ℤ
-- |
variable {R:@Rpoly G _ S _}
lemma monic_R_poly (u v: G) (h: u ≤ v) (R:@Rpoly G _ S _): Polynomial.Monic (R.R u v) ∧ Polynomial.degree (R.R u v)  = ℓ(v)-ℓ(u) ∧ Polynomial.constantCoeff (R.R u v) = (-1)^(ℓ(v)-ℓ(u)):=sorry

structure KLpoly where
P: G → G → Polynomial ℤ
not_le:∀(u v:G), ¬ (u ≤ v) → P u v = 0
eq:∀(u v:G), u = v → P u v = 1
deg_le_of_lt: ∀(u v:G), u < v → Polynomial.degree (P u v) ≤ ((ℓ(v)-ℓ(u)-1)/2:ℕ)
le:∀(u v:G), u ≤ v → X^(ℓ(v)-ℓ(u))* Polynomial.reverse (P u v) = (Finset.sum (BruhatInte u v) (fun a => R.R u a * P a v))* X^(Polynomial.natDegree (P u v))


lemma constant_eq_one_of_KL (u v :G) (h : u ≤ v) (KL:@KLpoly G _ S _ R): Polynomial.constantCoeff (KL.P u v) = 1:=sorry
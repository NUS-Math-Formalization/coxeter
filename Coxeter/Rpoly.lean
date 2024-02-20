import Coxeter.Basic
import Coxeter.Bruhat
import Coxeter.Length_reduced_word
import Coxeter.Hecke

import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Reverse
import Mathlib.Data.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Polynomial.Laurent

variable {G :(Type _)} [Group G] {S : (Set G)} [orderTwoGen S] [CoxeterSystem G S]

variable {w:G}

local notation :max "ℓ(" g ")" => (@length G  _ S _ g)
open Classical Hecke
-- class Rploy (u v:G)  (R_poly : Polynomial ℤ) where
--   not_le: ¬ (u ≤ v) → R_ploy = 0
--   eq: u = v → R_ploy = 1
--   sMemD_Ru: ∀ s ∈ D_R v, s∈D_R u → R_ploy = R
#check eps


class Rpoly' where
  R : G → G → LaurentPolynomial ℤ
  not_le:∀(u v:G), ¬ (u ≤ v) → R u v = 0

#check Rpoly'.R
@[ext]
structure Rpoly extends Rpoly' where
  eq:∀(u :G), R u u = 1
  sMemD_Ru: ∀(u v:G),s ∈ D_R v → s ∈ D_R u → R u v = R (u*s) (v*s)
  sNotMemD_Ru: ∀(u v:G),s ∈ D_R v → s ∉ D_R u → R u v = X*R (u*s) (v*s) + (X-1) * R u (v*s)

-- @[ext]
-- class Rpoly1 extends (CoxeterSystem G S) where
--   R : G → G → Polynomial ℤ
--   not_le:∀(u v:G), ¬ (u ≤ v) → R u v = 0
--   eq:∀(u :G),  R u u = 1
--   sMemD_Ru: ∀(u v:G),s ∈ D_R v → s ∈ D_R u → R u v = R (u*s) (v*s)
--   sNotMemD_Ru: ∀(u v:G),s ∈ D_R v → s ∉ D_R u → R u v = X*R (u*s) (v*s) + (X-1) * R u (v*s)

#check (Rpoly.toRpoly')

def inv_repr (R : G → G → LaurentPolynomial ℤ) := ∀ w : G, TTInv w⁻¹ = ( eps w * q ^ ℓ(w) ) • Finset.sum (Set.toFinset <| Bruhat.Iic w) (fun x => (eps x * R x w) • TT x)

def R' : G → G → Polynomial ℤ := sorry

theorem Hecke_invG_repr_aux : ∀ l, ∃ R : Rpoly',  ∀ w : G, l =ℓ(w) → TTInv w⁻¹ = ( eps w * q ^ ℓ(w) ) • Finset.sum (Set.toFinset <| Bruhat.Iic w) (fun x => (eps x * R.R x w) • TT x) := by
  intro l
  induction' l with n hn
  · sorry
  · rcases hn with ⟨R',hR'⟩



theorem Hecke_invG_repr : ∃ R : G → G → LaurentPolynomial ℤ, inv_repr R := by
  --induction' ℓ(w) with n hn
  sorry

lemma Rpoly_not_le (R : G → G → LaurentPolynomial ℤ) :  inv_repr R → ∀(u v:G), ¬ (u ≤ v) → R u v = 0 := sorry

lemma Rpoly_eq (R : G → G → LaurentPolynomial ℤ) :  inv_repr R → ∀(u :G),  R u u = 1 := by
  intro h
  sorry

lemma Rpoly_sMemD_Ru (R : G → G → LaurentPolynomial ℤ) :  inv_repr R → ∀(u v:G),s ∈ D_R v →
  s ∈ D_R u → R u v = R (u*s) (v*s) := sorry

lemma Rpoly_sNotMemD_Ru (R : G → G → LaurentPolynomial ℤ) :  inv_repr R → ∀(u v:G),s ∈ D_R v → s ∉ D_R u →
  R u v = X*R (u*s) (v*s) + (X-1) * R u (v*s) := sorry


-- lemma monic_R_poly (u v: G) (h: u ≤ v) (R:@Rpoly G _ S _): Polynomial.Monic (R.R u v) ∧ Polynomial.degree (R.R u v)  = ℓ(v)-ℓ(u) ∧ Polynomial.constantCoeff (R.R u v) = (-1)^(ℓ(v)-ℓ(u)):=sorry

instance : Rpoly (G := G) where
  R := @Classical.choose (G → G → LaurentPolynomial ℤ) inv_repr Hecke_invG_repr
  not_le := Rpoly_not_le (@Classical.choose (G → G → LaurentPolynomial ℤ) inv_repr Hecke_invG_repr) (Classical.choose_spec _)
  eq := Rpoly_eq (@Classical.choose (G → G → LaurentPolynomial ℤ) inv_repr Hecke_invG_repr) (Classical.choose_spec _)
  sMemD_Ru := _
  sNotMemD_Ru := _

variable {R:@Rpoly G _ S _}
instance : Unique (@Rpoly G _ S _) where
  default:= R
  uniq := by
    intro a
    ext u v n
    sorry

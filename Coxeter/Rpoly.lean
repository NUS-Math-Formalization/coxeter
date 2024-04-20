import Coxeter.Hecke
import Coxeter.BruhatOrder
--import Coxeter.Morphism

import Mathlib.LinearAlgebra.FreeModule.Basic

variable {G :(Type _)} [hG:CoxeterGroup G]

variable {w:G}
#check ℓ(w)


open Hecke CoxeterGroup CoxeterMatrix OrderTwoGen

local notation : max "q" => @LaurentPolynomial.T ℤ _ 1

local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)



class Rpoly (R : G → G → LaurentPolynomial ℤ) where
  not_le:∀(u v:G), ¬ (u ≤ v) → R u v = 0
  eq:∀(u :G),  R u u = 1
  mem_rD: ∀(u v:G),s ∈ rightDescent v → s ∈ rightDescent u → R u v = R (u*s) (v*s)
  not_mem_rD: ∀(u v:G),s ∈ rightDescent v → s ∉ rightDescent u → R u v = X*R (u*s) (v*s) + (X-1) * R u (v*s)

noncomputable def R (G : Type _) [CoxeterGroup G]: G → G → LaurentPolynomial ℤ := fun x w =>
  TTInv w⁻¹ x * (-1)^(ℓ(w) + (ℓ(x))) * q^(ℓ(w))

lemma coeff_eq (h : Hecke G) (w : G) (s : hG.S): ℓ(w) < ℓ(s*w) → ((TT s.1) * h) (s*w) = h w:=sorry

lemma Rpoly_eq' : ∀ l, ∀ w : G, l = ℓ(w) → TTInv w⁻¹ w = q⁻¹^(ℓ(w)) := by
  intro l
  induction' l with n hn
  · sorry
  · intro w hw
    have : ℓ(w) ≠ 0 := by simp [←hw]
    have : w ≠ 1 := Function.mt length_zero_iff_one.2 this
    let s:= Classical.choice (leftDescent_NE_of_ne_one this)
    have hleq : ℓ(s*w) = n := sorry
    sorry

lemma Rpoly_eq (w : G): TTInv w⁻¹ w = q⁻¹^(ℓ(w)) := sorry

instance : Rpoly (R G) where
  not_le := sorry
  eq := sorry
  mem_rD := sorry
  not_mem_rD := sorry


-- theorem Hecke_invG_repr_aux : ∀ l, ∃ R : Rpoly',  ∀ w : G, l =ℓ(w) → TTInv w⁻¹ = ( eps w * q ^ (ℓ(w)) ) • Finset.sum (Set.toFinset <| Bruhat.Iic w) (fun x => (eps x * R.R x w) • TT x) := by
--   intro l
--   induction' l with n hn
--   · sorry
--   · rcases hn with ⟨R',hR'⟩

-- theorem Hecke_invG_repr : ∃ R : G → G → LaurentPolynomial ℤ, inv_repr R := by
--   --induction' ℓ(w) with n hn
--   sorry

-- lemma Rpoly_not_le (R : G → G → LaurentPolynomial ℤ) :  inv_repr R → ∀(u v:G), ¬ (u ≤ v) → R u v = 0 := sorry

-- lemma Rpoly_eq (R : G → G → LaurentPolynomial ℤ) :  inv_repr R → ∀(u :G),  R u u = 1 := by
--   intro h
--   sorry

-- lemma Rpoly_sMemD_Ru (R : G → G → LaurentPolynomial ℤ) :  inv_repr R → ∀(u v:G),s ∈ rightDescent v →
--   s ∈ rightDescent u → R u v = R (u*s) (v*s) := sorry

-- lemma Rpoly_sNotMemD_Ru (R : G → G → LaurentPolynomial ℤ) :  inv_repr R → ∀(u v:G),s ∈ rightDescent v → s ∉ rightDescent u →
--   R u v = X*R (u*s) (v*s) + (X-1) * R u (v*s) := sorry


-- -- lemma monic_R_poly (u v: G) (h: u ≤ v) (R:@Rpoly G _ S _): Polynomial.Monic (R.R u v) ∧ Polynomial.degree (R.R u v)  = ℓ(v)-ℓ(u) ∧ Polynomial.constantCoeff (R.R u v) = (-1)^(ℓ(v)-ℓ(u)):=sorry

-- instance : Rpoly (G := G) where
--   R := @Classical.choose (G → G → LaurentPolynomial ℤ) inv_repr Hecke_invG_repr
--   not_le := Rpoly_not_le (@Classical.choose (G → G → LaurentPolynomial ℤ) inv_repr Hecke_invG_repr) (Classical.choose_spec _)
--   eq := Rpoly_eq (@Classical.choose (G → G → LaurentPolynomial ℤ) inv_repr Hecke_invG_repr) (Classical.choose_spec _)
--   sMemD_Ru := _
--   sNotMemD_Ru := _

-- variable {R:@Rpoly G _ S _}
-- instance : Unique (Rpoly (G:=G) ) where
--   default:= R
--   uniq := by
--     intro a
--     ext u v n
--     sorry

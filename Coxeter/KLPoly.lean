import Coxeter.Hecke

namespace Hecke

variable {G :(Type _)} [hG:CoxeterGroup G] {w : G}

noncomputable def involution_aux : G → Hecke G := fun w => TTInv w⁻¹

noncomputable def involution : Hecke G → Hecke G := fun h => Finsupp.mapRange LaurentPolynomial.invert (by simp) ((Finsupp.total G (Hecke G) (LaurentPolynomial ℤ)  involution_aux) h)

local notation  "ι" => involution

namespace involution

variable {s : hG.S} {w : G} {r : LaurentPolynomial ℤ}

lemma apply_single : involution (TT w) = TTInv w⁻¹ := sorry

lemma apply : involution (r • TT w) = (LaurentPolynomial.invert r) • TTInv w⁻¹ := sorry

lemma apply_smul_of_length_gt (h : ℓ(w) < ℓ(s*w)) : ι (TT s.1 * TT w) = ι (TT s.1) * ι (TT w) := sorry

lemma apply_smul_of_length_lt (h : ℓ(s*w) < ℓ(w)) : ι (TT s.1 * TT w) = ι (TT s.1) * ι (TT w) := sorry

lemma order_two : (ι : Hecke G → Hecke G) ^2 = 1 := sorry

noncomputable instance : RingHom (Hecke G) (Hecke G) where
  toFun := involution
  map_one' := by sorry
  map_mul' := sorry
  map_zero' := by simp;sorry
  map_add' := sorry

end involution

end Hecke

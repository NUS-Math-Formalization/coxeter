import Coxeter.Hecke.Hecke
import Coxeter.Hecke.Lemmas
import Coxeter.OrderTwoGen

namespace Hecke

variable {G :(Type _)} [hG:CoxeterGroup G] {w : G}

noncomputable def involution_aux : G → Hecke G := fun w => TTInv w⁻¹

noncomputable def involution : Hecke G → Hecke G := fun h => Finsupp.total G (Hecke G) (LaurentPolynomial ℤ) involution_aux (Finsupp.mapRange LaurentPolynomial.invert (by simp) h)

local notation  "ι" => involution

namespace involution

variable {s : hG.S} {w : G} {r : LaurentPolynomial ℤ}

lemma apply_single : ι (TT w) = TTInv w⁻¹ := by
  simp only [involution,Finsupp.total_apply,involution_aux]
  rw [TT,Finsupp.mapRange_single]
  simp only [map_one, zero_smul, Finsupp.sum_single_index, one_smul]

lemma apply : ι (r • TT w) = (LaurentPolynomial.invert r) • TTInv w⁻¹ := by
  simp only [involution,TT]
  rw [Finsupp.smul_single,Finsupp.mapRange_single]
  simp only [smul_eq_mul, _root_.mul_one, Finsupp.total_single,involution_aux]

lemma apply_smul_of_length_gt (h : ℓ(w) < ℓ(s*w)) : ι (TT s.1 * TT w) = ι (TT s.1) * ι (TT w) := by
  rw [mul_gt s h]
  simp only [apply_single, mul_inv_rev, OrderTwoGen.inv_eq_self'']
  rw [TTInv_muls_of_length_gt']
  rw [HOrderTwoGenGroup.length,←OrderTwoGen.length_eq_inv_length (S:=hG.S) (g:=w)]
  rw [HOrderTwoGenGroup.length,OrderTwoGen.length_eq_inv_length (S:=hG.S) (g:= w⁻¹*s)]
  simp only [mul_inv_rev, OrderTwoGen.inv_eq_self'', inv_inv]
  assumption

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

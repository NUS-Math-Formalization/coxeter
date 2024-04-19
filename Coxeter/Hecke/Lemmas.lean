import Coxeter.Hecke.Hecke
import Coxeter.CoxeterMatrix.Lemmas

variable {G :(Type _)} [hG:CoxeterGroup G] {w : G} {s : hG.S}

local notation : max "q" => @LaurentPolynomial.T ℤ _ 1

local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)

open Hecke

--trans to CoxeterMatrix.Lemmas
lemma mul_SimpleRefl_ne_self : w * s ≠ w := sorry

lemma Hecke_apply_eq_total_apply {h : Hecke G} {w : G} : h w = (Finsupp.total G (Hecke G) (LaurentPolynomial ℤ) TT) h w := sorry

lemma muls_apply_antidiagonal_of_memrD_aux {x w : G} {s : hG.S} (h1 : ℓ(w*s) < ℓ(w)) :
  (TT x * TT s.1) w ≠ 0 ↔ x = w ∨ x = w*s := sorry

lemma smul_apply {h: Hecke G} {r: LaurentPolynomial ℤ} (w:G) : (r • h) w = r * h w := by
  rw [Finsupp.smul_apply]
  rfl

lemma sub_apply (h1 h2: Hecke G) (w:G) : (h1 - h2) w = h1 w - h2 w :=by
  rw [←Finsupp.sub_apply h1 h2 w]
  sorry

lemma muls_apply_antidiagonal_of_memrD (h : Hecke G) (s : hG.S) (w : G) (h1 : ℓ(w*s) < ℓ(w)) : (h * TT s.1) w = (q-1) * h w + h (w*s) := by
    nth_rw 1 [repr_respect_TT h,Finsupp.sum_mul,Finsupp.sum_apply]
    rw [Finsupp.sum_of_support_subset h (s:=h.support) (by simp) ]
    have : ∀ c ∈ h.support, c ≠ w ∧ c ≠ w * ↑s → (h c • TT c * TT s.1) w = 0 := by
      intro c _ hcc
      rw [smul_mul_assoc,Finsupp.smul_apply]
      have : (TT c * TT s.1) w = 0 := by
        have hcc' : ¬(c = w ∨ c = w * ↑s) := by push_neg;assumption
        have := Function.mt (muls_apply_antidiagonal_of_memrD_aux (x:=c) h1).1 hcc'
        simp at this
        assumption
      rw [this,smul_zero]
    have h1' :ℓ(w*s) < ℓ(w*s*s) := by nth_rw 2 [←muls_twice w s] at h1;assumption
    rw [Finset.sum_eq_add w (w*s) (ne_comm.1 mul_SimpleRefl_ne_self) this]
    simp
    rw [mul_lt' s h1,mul_gt' s h1',smul_apply,Finsupp.add_apply,mul_add,smul_apply,TT_apply_self,smul_apply,TT_apply_ne_self]
    simp_rw [muls_twice,smul_apply,TT_apply_self]
    ring
    exact mul_SimpleRefl_ne_self
    · intro hw; rw [Finsupp.not_mem_support_iff] at hw; rw [hw]; simp; exact Finsupp.zero_apply
    · intro hw; rw [Finsupp.not_mem_support_iff] at hw; rw [hw]; simp; exact Finsupp.zero_apply
    intro i
    simp

lemma muls_apply_antidiagonal_of_not_memrD (h : Hecke G) (s : hG.S) (w : G) (h1 : ℓ(w) < ℓ(w*s)) :  (h * TT s.1) w = q * h (w*s) := sorry

@[simp] lemma TTInv_one : TTInv (1:G) = 1 := by
  have h2: TT (1:G) * TT 1 = 1 := by rw [←one_def,_root_.one_mul]
  rw [←(TTInv_unique h2)]
  rfl

lemma TTInv_muls_of_length_gt' {s:hG.S} (h: ℓ(w) < ℓ(w*s)): TTInv (w*s) = TTInv s.1 * TTInv w := sorry

lemma TTInv_muls_of_length_gt (s:hG.S) (h: ℓ(w) < ℓ(s*w)): TTInv (s.1*w) = TTInv w * TTInv s.1:= by
  suffices h1 : TTInv (s.1*w) * TT (s.1*w) = TTInv w * TTInv s.1 * TT (s.1*w) from by
    have h2 : TTInv (s.1*w) * TT (s.1*w) * TTInv (s.1*w) = TTInv w * TTInv s.1 * TT (s.1*w) * TTInv (s.1*w)
    := by rw [h1]
    rw [_root_.mul_assoc,mul_TTInv,_root_.mul_assoc,mul_TTInv] at h2
    simp at h2
    assumption
  rw [TTInv_mul,←mul_gt _ h,_root_.mul_assoc,←_root_.mul_assoc (TTInv s.1),TTInv_mul]
  simp [TTInv_mul]

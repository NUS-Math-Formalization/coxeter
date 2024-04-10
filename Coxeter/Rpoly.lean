import Coxeter.Hecke
import Coxeter.BruhatOrder
--import Coxeter.Morphism

import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Reverse
import Mathlib.Data.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Polynomial.Laurent

variable {G :(Type _)} [hG:CoxeterGroup G]

open Hecke CoxeterGroup CoxeterMatrix OrderTwoGen Classical Bruhat

local notation : max "q" => @LaurentPolynomial.T ℤ _ 1
local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)
#check SimpleRefl_is_Refl

-- trans to ...
lemma length_induction {p : G → Prop} {w: G} {s:rightDescent w} (hw: w ≠ 1) (h1 : p 1) (hws : p (w*s) → p w) : ∀ u:G, p u := sorry

-- trans to CoxeterSystem
lemma mul_SimpleRefl_twice (w:G) (s: hG.S) : w = w*s*s := by
  rw [mul_assoc,gen_square_eq_one' s,mul_one]

lemma mem_rightDescent_of_length_muls_lt {w:G} {s: hG.S} (h: ℓ(w*s) < ℓ(w)) : s.1 ∈ rightDescent w := by
  sorry

lemma mem_rD_mul_of_not_mem_rD {w:G} {s: hG.S} (h: s.1 ∉ rightDescent w) : s.1 ∈ rightDescent (w*s):= by
  sorry

--trans to BruhatOrder
lemma eq_one_of_le_one {w:G} : w ≤ 1 → w = 1 := by
  intro h
  sorry

lemma mul_lt_of_mem_rD {v :G} {s: hG.S} (h: s.1 ∈ rightDescent v) : v*s < v := by
  have hlt : lt_adj (v*s) v := by
    rw [lt_adj]
    use s.1
    exact ⟨SimpleRefl_is_Refl s.2, ⟨mul_SimpleRefl_twice v s, length_muls_lt_of_mem_rightDescent ⟨s.1,h⟩⟩⟩
  exact (Relation.transGen_iff lt_adj (v*s) v).2 (Or.inl hlt)

lemma mul_gt_of_not_mem_rD {v :G} {s: hG.S} (h: s.1 ∉ rightDescent v) : v < v*s := by
  nth_rw 1 [mul_SimpleRefl_twice v s]
  exact mul_lt_of_mem_rD (mem_rD_mul_of_not_mem_rD h)

lemma le_cancel_of_not_mem_rD {u v :G} {s: hG.S} (h1: s.1 ∉ rightDescent u) (h2: s.1 ∈ rightDescent v) :
  u*s ≤ v*s → u ≤ v := by
    have h := le_of_lt (mul_gt_of_not_mem_rD h1)
    have h' := le_of_lt (mul_lt_of_mem_rD h2 )
    intro h''
    exact le_trans (le_trans h h'') h'

--use subword property
lemma le_cancel_of_mem_rD {u v :G} {s: hG.S} (h1: s.1 ∈ rightDescent u) (h2: s.1 ∈ rightDescent v) :
  u*s ≤ v*s → u ≤ v := by
    sorry

-- trans to Hecke
lemma muls_apply_antidiagonal_of_memrD (h : Hecke G) (s : hG.S) (w : G) (h1 : ℓ(w*s) < ℓ(w)) :
  (h * TT s.1) w = (q-1) * h w + h (w*s) := by
    sorry

lemma muls_apply_antidiagonal_of_not_memrD (h : Hecke G) (s : hG.S) (w : G) (h1 : ℓ(w) < ℓ(w*s)) :
    (h * TT s.1) w = q * h (w*s) := sorry

@[simp] lemma TTInv_one : TTInv (1:G) = 1 := by
  have h2: TT (1:G) * TT 1 = 1 := by rw [←one_eq,one_mul]
  rw [←(TTInv_unique h2)]
  rfl

lemma TTInv_muls_of_length_gt {s:hG.S} (h: ℓ(w) < ℓ(w*s)): TTInv (w*s) = TTInv s.1 * TTInv w := sorry

lemma TTInv_muls_of_length_gt' (s:hG.S) (h: ℓ(w) < ℓ(s*w)): TTInv (s.1*w) = TTInv w * TTInv s.1:= by
  suffices h1 : TTInv (s.1*w) * TT (s.1*w) = TTInv w * TTInv s.1 * TT (s.1*w) from by
    have h2 : TTInv (s.1*w) * TT (s.1*w) * TTInv (s.1*w) = TTInv w * TTInv s.1 * TT (s.1*w) * TTInv (s.1*w)
    := by rw [h1]
    rw [mul_assoc,mul_TTInv,mul_assoc,mul_TTInv] at h2
    simp at h2
    assumption
  rw [TTInv_mul,←mul_gt _ h,mul_assoc,←mul_assoc (TTInv s.1),TTInv_mul]
  simp [TTInv_mul]

class Rpoly (R : G → G → LaurentPolynomial ℤ) where
  not_le:∀(u v:G), ¬ (u ≤ v) → R u v = 0
  eq:∀(u :G),  R u u = 1
  mem_rD: ∀(u v:G),s ∈ rightDescent v → s ∈ rightDescent u → R u v = R (u*s) (v*s)
  not_mem_rD: ∀(u v:G),s ∈ rightDescent v → s ∉ rightDescent u → R u v = q*R (u*s) (v*s) + (q-1) * R u (v*s)

--noncomputable def R (G : Type _) [CoxeterGroup G]: G → G → LaurentPolynomial ℤ := fun x w =>
--  ite (x ≤ w) ( TTInv w⁻¹ x * (-1)^(ℓ(w) + (ℓ(x))) * q^(ℓ(w)) ) 0

noncomputable def R (G : Type _) [CoxeterGroup G]: G → G → LaurentPolynomial ℤ := fun x w =>
  ( TTInv w⁻¹ x * (-1)^(ℓ(w) + (ℓ(x))) * q^(ℓ(w)) )

lemma Rpoly_aux {u v :G} (h1:s ∈ rightDescent v) (h2:s ∈ rightDescent u):
    (TTInv v⁻¹) u * q = (TTInv (v * s)⁻¹) (u * s) := by
      have sss : s ∈ hG.S := Set.mem_of_mem_inter_right h1
      have hl : ℓ((v * s)⁻¹) < ℓ(s * (v * s)⁻¹) := sorry
      nth_rw 1 [mul_SimpleRefl_twice u ⟨s,sss⟩ ,mul_SimpleRefl_twice v ⟨s,sss⟩]
      rw [mul_inv_rev,←inv_eq_self' ⟨s,sss⟩,TTInv_muls_of_length_gt' ⟨s,sss⟩ hl]
      rw [TTInv_s_eq]
      -- simp only [Subtype.coe_mk]
      -- rw [mul_sub (TTInv (v * s)⁻¹) (q⁻¹ • TT s) (1 - q⁻¹) • 1]
      sorry

lemma Rpoly_mem_rD : ∀(u v:G),s ∈ rightDescent v → s ∈ rightDescent u → R G u v = R G (u*s) (v*s) := by
  intro u v h1 h2
  by_cases hn : Nonempty (rightDescent v)
  · by_cases hn' : Nonempty (rightDescent u)
    · rw [R,R]
      have hlvs : ℓ(v*s) + 1 = ℓ(v) := by
        rw [length_muls_of_mem_rightDescent ⟨s,h1⟩,←Nat.pred_eq_sub_one,←Nat.succ_eq_add_one,Nat.succ_pred]
        exact Function.mt length_zero_iff_one.1 (rightDescent_NE_iff_ne_one.2 hn)
      rw [←Rpoly_aux h1 h2]
      have hlus : ℓ(u*s) + 1 = ℓ(u) := by
        rw [length_muls_of_mem_rightDescent ⟨s,h2⟩,←Nat.pred_eq_sub_one,←Nat.succ_eq_add_one,Nat.succ_pred]
        exact Function.mt length_zero_iff_one.1 (rightDescent_NE_iff_ne_one.2 hn')
      have hlusv : ℓ(v) + ℓ(u) = ℓ(v*s) + ℓ(u*s) + 2:= by rw [←hlvs,←hlus];ring
      rw [hlusv,pow_add,neg_one_pow_two,mul_one,←hlvs,pow_add q,pow_one]
      ring
    · have : Nonempty (rightDescent u) := Nonempty.intro ⟨s,h2⟩
      contradiction
  · have : Nonempty (rightDescent v) := Nonempty.intro ⟨s,h1⟩
    contradiction

lemma Rpoly_not_mem_rD : ∀(u v:G),s ∈ rightDescent v → s ∉ rightDescent u →
  R G u v = q*R G (u*s) (v*s) + (q-1) * R G u (v*s) := by
    intro u v hsv hsu
    by_cases hn : Nonempty (rightDescent v)
    · rw [R,R,R]
      have sss : s ∈ hG.S := Set.mem_of_mem_inter_right hsv
      have vss : v = v*s*s := by rw [mul_assoc,gen_square_eq_one' ⟨s,sss⟩,mul_one]
      have hl : ℓ((v * s)⁻¹) < ℓ(s * (v * s)⁻¹) := by
        rw [mul_inv_rev]
        simp
        rw [←mul_inv_rev,]
        repeat
          rw [HOrderTwoGenGroup.length,←length_eq_inv_length (S:=hG.S)]
        have : v ≠ 1 := rightDescent_NE_iff_ne_one.2 hn
        rw [←HOrderTwoGenGroup.length,length_muls_of_mem_rightDescent ⟨s,hsv⟩]
        have h': 0 < ℓ(v) := Nat.ne_zero_iff_zero_lt.1 (Function.mt length_zero_iff_one.1 this)
        rw [←HOrderTwoGenGroup.length,←Nat.pred_eq_sub_one]
        exact Nat.pred_lt_self h'
      rw [vss,mul_inv_rev,←inv_eq_self' ⟨s,sss⟩,TTInv_muls_of_length_gt' ⟨s,sss⟩ hl,TTInv_s_eq]
      calc
        _ = (TTInv (v * s)⁻¹ * (q⁻¹ • TT s) - TTInv (v * s)⁻¹ * (1 - q⁻¹) • 1) u *
        (-1) ^(ℓ(v * s * s) + ℓ(u)) * q ^ ℓ(v * s * s) := by sorry
        _ = _ := sorry
    · have : Nonempty (rightDescent v) := Nonempty.intro ⟨s,hsv⟩
      contradiction

lemma Rpoly_not_le : ∀(u v:G), ¬ (u ≤ v) → R G u v = 0 := by
  intro u v
  by_cases hv : v = 1
  · rw [hv]
    intro h
    have h' : u ≠ 1 := by intro h''; exact h (by rw [h''])
    simp [R]
    exact Or.inl (TT_apply_ne_self (ne_comm.1 h'))
  · have h1 : ∀ u,¬u ≤ 1 → R G u 1 = 0 := by
      intro uu huu
      have h' : uu ≠ 1 := by intro h''; exact huu (by rw [h''])
      simp [R]
      exact Or.inl (TT_apply_ne_self (ne_comm.1 h'))
    have hrDv : Nonempty (rightDescent v) := rightDescent_NE_iff_ne_one.1 hv
    let s := Classical.choice hrDv
    let p := fun v => (∀ u, ¬u ≤ v → R G u v = 0)
    have hws : (∀ u, ¬u ≤ (v*s) → R G u (v*s) = 0) → (∀ u, ¬u ≤ v → R G u v = 0) := by
      intro h u huv
      have sss : s.1 ∈ hG.S := Set.mem_of_mem_inter_right s.2
      by_cases hsv : s.1 ∈ (rightDescent u)
      · rw [Rpoly_mem_rD u v s.2 hsv]
        contrapose huv
        have h2 := Function.mt (h (u*s)) huv
        push_neg at *
        exact le_cancel_of_mem_rD (s:= ⟨s.1,sss⟩) hsv s.2 h2
      · rw [Rpoly_not_mem_rD u v s.2 hsv]
        have himp1 : u*s ≤ v*s → u ≤ v := by
          intro hh
          exact le_cancel_of_not_mem_rD (s:= ⟨s.1,sss⟩) hsv s.2 hh
        have himp2 : u ≤ v*s → u ≤ v := by
          intro hh
          have := le_of_lt (mul_lt_of_mem_rD (s:= ⟨s.1,sss⟩) (v:=v) s.2)
          rw [Subtype.coe_mk] at this
          exact le_trans hh this
        have hi1 := h (u*s) (Function.mt himp1 huv)
        have hi2 := h u (Function.mt himp2 huv)
        rw [hi1,hi2]
        simp
    exact length_induction (p:=p) hv h1 hws v u

lemma Rpoly_eq' : ∀ l, ∀ w : G, l = ℓ(w) → TTInv w⁻¹ w = q⁻¹^(ℓ(w)) := by
  intro l
  induction' l with n hn
  · intro w hw
    have : w = 1 := length_zero_iff_one.1 (eq_comm.1 hw)
    rw [this,inv_one,TTInv_one,←this,←hw,this,one_eq]
    simp [TT_apply_ne_self]
  · intro w hw
    have : ℓ(w) ≠ 0 := by simp [←hw]
    have wne1: w ≠ 1 := Function.mt length_zero_iff_one.2 this
    let s:= Classical.choice (rightDescent_NE_of_ne_one wne1)
    have hsmem: s.1 ∈ (rightDescent w) := by simp
    have hleq : ℓ(w*s) = n := by
      rw [length_muls_of_mem_rightDescent s,←hw]
      simp
    have hypo := hn (w*s) (eq_comm.1 hleq)
    rw [←Rpoly_aux hsmem hsmem] at hypo
    have hlw : ℓ(w) = ℓ(w*s) + 1 := by linarith
    rw [hlw,pow_add,←hypo,pow_one,mul_assoc,←LaurentPolynomial.T_add]
    simp

lemma Rpoly_eq : ∀ (u : G), R G u u = 1 := by
  intro u
  rw [R]
  simp
  have := Rpoly_eq' ℓ(u) u (rfl)
  rw [this,LaurentPolynomial.T_pow,←LaurentPolynomial.T_add]
  simp

instance : Rpoly (R G) where
  not_le := Rpoly_not_le
  eq := Rpoly_eq
  mem_rD := Rpoly_mem_rD
  not_mem_rD := Rpoly_not_mem_rD


lemma Unique_Rpoly {R' : G → G → LaurentPolynomial ℤ}: Rpoly R' → R' = R G := by
  intro h
  funext u v
  have h1 : ∀ u, R' u 1 = R G u 1 := by
    intro u
    by_cases h' : u = 1
    · rw [h',Rpoly.eq (R:=R'),Rpoly_eq]
    · have h'' : ¬ u ≤ 1 := by
        contrapose h'
        push_neg at *
        exact eq_one_of_le_one h'
      rw [Rpoly.not_le (R:=R'),Rpoly_not_le _ _ h'']
      assumption
  by_cases hv1 : v = 1
  · rw [hv1]
    exact h1 u
  · let s := choice (rightDescent_NE_of_ne_one hv1)
    let p := fun v => ∀ u, R' u v = R G u v
    have hws : (∀ u, R' u (v*s) = R G u (v*s))→ ∀ u, R' u v = R G u v := by
      intro h'
      intro u
      by_cases hus : s.1 ∈ rightDescent u
      · rw [Rpoly.mem_rD (R:=R') _ _ s.2 hus,Rpoly_mem_rD _ _ s.2 hus]
        exact h' (u*s)
      · rw [Rpoly.not_mem_rD (R:=R') _ _ s.2 hus,Rpoly_not_mem_rD _ _ s.2 hus]
        rw [h' (u*s),h' u]
    exact length_induction (p:=p) hv1 h1 hws v u

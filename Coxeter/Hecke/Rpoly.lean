import Coxeter.Hecke.Hecke
import Coxeter.Hecke.Lemmas
import Coxeter.BruhatOrder
import Coxeter.CoxeterMatrix.Lemmas
--import Coxeter.Morphism

import Mathlib.LinearAlgebra.FreeModule.Basic

variable {G :(Type _)} [hG:CoxeterGroup G]

open Hecke CoxeterGroup CoxeterMatrix OrderTwoGen Classical Bruhat

local notation : max "q" => @LaurentPolynomial.T ℤ _ 1
local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)

-- trans to CoxeterSystem
lemma mul_SimpleRefl_twice (w:G) (s: hG.S) : w = w*s*s := by
  rw [_root_.mul_assoc,gen_square_eq_one' s,_root_.mul_one]

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
    exact ⟨SimpleRefl_is_Refl s.2, ⟨mul_SimpleRefl_twice v s, Set.mem_setOf.1 (Set.mem_of_mem_inter_left h).2 ⟩⟩
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

class Rpoly (R : G → G → LaurentPolynomial ℤ) where
  not_le:∀(u v:G), ¬ (u ≤ v) → R u v = 0
  eq:∀(u :G),  R u u = 1
  mem_rD: ∀(u v:G) (s:hG.S),s.1 ∈ rightDescent v → s.1 ∈ rightDescent u → R u v = R (u*s) (v*s)
  not_mem_rD: ∀(u v:G) (s:hG.S),s.1 ∈ rightDescent v → s.1 ∉ rightDescent u → R u v = q*R (u*s) (v*s) + (q-1) * R u (v*s)

noncomputable def R (G : Type _) [CoxeterGroup G]: G → G → LaurentPolynomial ℤ := fun x w =>
  ( TTInv w⁻¹ x * (-1)^(ℓ(w) + (ℓ(x))) * q^(ℓ(w)) )

lemma Rpoly_aux {u v :G} {s:hG.S} (h1:s.1 ∈ rightDescent v) (h2:s.1 ∈ rightDescent u):
    (TTInv v⁻¹) u * q = (TTInv (v * s)⁻¹) (u * s) := by
      have hl : ℓ((v * s)⁻¹) < ℓ(s * (v * s)⁻¹) := sorry
      nth_rw 1 [mul_SimpleRefl_twice v s]
      rw [mul_inv_rev,←inv_eq_self' s,TTInv_muls_of_length_gt (s:=s) hl]
      rw [TTInv_s_eq,mul_sub,sub_apply,mul_smul_comm,smul_apply,muls_apply_antidiagonal_of_memrD]
      sorry
      sorry

lemma Rpoly_eq' : ∀ l, ∀ w : G, l = ℓ(w) → TTInv w⁻¹ w = q⁻¹^(ℓ(w)) := by
  intro l
  induction' l with n hn
  · intro w hw
    have : w = 1 := length_zero_iff_one.1 (eq_comm.1 hw)
    rw [this,inv_one,TTInv_one,←this,←hw,this,one_def]
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
    have smemS : s.1 ∈ hG.S := Set.mem_of_mem_inter_right s.2
    rw [←Rpoly_aux (s:=⟨s.1,smemS⟩) hsmem hsmem] at hypo
    have hlw : ℓ(w) = ℓ(w*s) + 1 := by linarith
    rw [hlw,pow_add,←hypo,pow_one,_root_.mul_assoc,←LaurentPolynomial.T_add]
    simp

lemma Rpoly_eq : ∀ (u : G), R G u u = 1 := by
  intro u
  rw [R]
  simp
  have := Rpoly_eq' (ℓ(u)) u (rfl)
  rw [this,LaurentPolynomial.T_pow,←LaurentPolynomial.T_add]
  simp

lemma Rpoly_mem_rD : ∀(u v:G) (s:hG.S),s.1 ∈ rightDescent v → s.1 ∈ rightDescent u → R G u v = R G (u*s) (v*s) := by
  intro u v s h1 h2
  by_cases hn : Nonempty (rightDescent v)
  · by_cases hn' : Nonempty (rightDescent u)
    · rw [R,R]
      have hlvs : ℓ(v*s) + 1 = ℓ(v) := by
        rw [length_muls_of_mem_rightDescent ⟨s.1,h1⟩,←Nat.pred_eq_sub_one,←Nat.succ_eq_add_one,Nat.succ_pred]
        exact Function.mt length_zero_iff_one.1 (ne_one_of_rightDescent_NE hn)
      rw [←Rpoly_aux h1 h2]
      have hlus : ℓ(u*s) + 1 = ℓ(u) := by
        rw [length_muls_of_mem_rightDescent ⟨s.1,h2⟩,←Nat.pred_eq_sub_one,←Nat.succ_eq_add_one,Nat.succ_pred]
        exact Function.mt length_zero_iff_one.1 (ne_one_of_rightDescent_NE hn')
      have hlusv : ℓ(v) + (ℓ(u)) = ℓ(v*s) + (ℓ(u*s)) + 2:= by rw [←hlvs,←hlus];ring
      rw [hlusv,pow_add,neg_one_pow_two,_root_.mul_one,←hlvs,pow_add q,pow_one]
      ring
    · have : Nonempty (rightDescent u) := Nonempty.intro ⟨s,h2⟩
      contradiction
  · have : Nonempty (rightDescent v) := Nonempty.intro ⟨s,h1⟩
    contradiction

lemma Rpoly_not_mem_rD : ∀(u v:G) (s:hG.S),s.1 ∈ rightDescent v → s.1 ∉ rightDescent u →
  R G u v = q*R G (u*s) (v*s) + (q-1) * R G u (v*s) := by
    intro u v s hsv hsu
    by_cases hn : Nonempty (rightDescent v)
    · rw [R,R,R]
      have vss : v = v*s*s := by rw [_root_.mul_assoc,gen_square_eq_one' s,_root_.mul_one]
      have hl : ℓ((v * s)⁻¹) < ℓ(s * (v * s)⁻¹) := by
        rw [mul_inv_rev]
        simp
        rw [inv_eq_self',←mul_inv_rev]
        repeat
          rw [HOrderTwoGenGroup.length,←length_eq_inv_length (S:=hG.S)]
        have : v ≠ 1 := ne_one_of_rightDescent_NE hn
        rw [←HOrderTwoGenGroup.length,length_muls_of_mem_rightDescent ⟨s.1,hsv⟩]
        have h': 0 < ℓ(v) := Nat.ne_zero_iff_zero_lt.1 (Function.mt length_zero_iff_one.1 this)
        rw [←Nat.pred_eq_sub_one,←mul_inv_rev,_root_.mul_assoc]
        simp
        rw [HOrderTwoGenGroup.length,length_eq_inv_length (S:=hG.S)] at *
        exact Nat.pred_lt_self h'
      nth_rw 1 [vss]
      rw [mul_inv_rev,←inv_eq_self' s,TTInv_muls_of_length_gt (s:=s) hl,TTInv_s_eq]
      calc
        _ = (TTInv (v * s)⁻¹ * (q⁻¹ • TT s.1) - TTInv (v * s)⁻¹ * (1 - q⁻¹) • 1) u *
        (-1) ^(ℓ(v * s * s) + (ℓ(u)) ) * q ^ (ℓ(v * s * s)) := by rw [mul_sub,←vss]
        _ = _ := by sorry
    · have : Nonempty (rightDescent v) := Nonempty.intro ⟨s,hsv⟩
      contradiction

lemma Rpoly_not_le : ∀(u v:G), ¬ (u ≤ v) → R G u v = 0 := by
  intro u v
  have h1 : ∀ u,¬u ≤ 1 → R G u 1 = 0 := by
    intro uu huu
    have h' : uu ≠ 1 := by intro h''; exact huu (by rw [h''])
    simp [R]
    exact Or.inl (TT_apply_ne_self (ne_comm.1 h'))
  let p := fun v => (∀ u, ¬u ≤ v → R G u v = 0)
  have hws : ∀ w, ∀s:hG.S, s.1 ∈ rightDescent w → p (w*s) → p w := by
    intro w s hsw pws
    dsimp [p] at *
    intro u huv
    by_cases hsu : s.1 ∈ (rightDescent u)
    · rw [Rpoly_mem_rD u w s hsw hsu]
      contrapose huv
      have h2 := Function.mt (pws (u*s)) huv
      push_neg at *
      exact le_cancel_of_mem_rD hsu hsw h2
    · rw [Rpoly_not_mem_rD u w s hsw hsu]
      have himp1 : u*s ≤ w*s → u ≤ w := by exact le_cancel_of_not_mem_rD hsu hsw
      have himp2 : u ≤ w*s → u ≤ w := by
        intro hh
        have : w*s ≤ w := le_of_lt (mul_lt_of_mem_rD hsw)
        exact le_trans hh this
      have hi1 := pws (u*s) (Function.mt himp1 huv)
      have hi2 := pws u (Function.mt himp2 huv)
      rw [hi1,hi2]
      simp
  exact length_induction (p:=p) h1 hws v u

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
  let p := fun v => ∀ u, R' u v = R G u v
  have hws : ∀ v, ∀s:hG.S, s.1 ∈ rightDescent v → (∀ u, R' u (v*s) = R G u (v*s))→ ∀ u, R' u v = R G u v := by
    intro v s smemrD h' u
    by_cases hus : s.1 ∈ rightDescent u
    · rw [Rpoly.mem_rD (R:=R') _ _ _ smemrD hus,Rpoly_mem_rD _ _ _ smemrD hus]
      exact h' (u*s)
    · rw [Rpoly.not_mem_rD (R:=R') _ _ _ smemrD hus,Rpoly_not_mem_rD _ _ _ smemrD hus]
      rw [h' (u*s),h' u]
  exact length_induction (p:=p) h1 hws v u

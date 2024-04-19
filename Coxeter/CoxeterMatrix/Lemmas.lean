import Coxeter.CoxeterMatrix.CoxeterSystem

/-!
# Lemmas
This file provides extra lemmas when an `OrderTwoGen` group `G` is also a `CoxeterGroup`.
-/

open CoxeterGroup
open OrderTwoGen

variable {G : Type*} {w : G} [hG:CoxeterGroup G]

-- following lemmas assume G is CoxeterGroup, we can also have CoxeterMatrix version.
-- these lemmas are needed in Hecke.lean, because the def of Hecke use [CoxeterGroup G],
-- for convenience, the statements also use [CoxeterGroup G]
-- some lemmas are symmetric, such as muls_twice : w*s*s = w, the symm version is s*s*w = w.
-- this section only contain lemmas that needed in Hecke.lean, you can also formulate the symms if u want.


lemma leftDescent_NE_of_ne_one (h : w ≠ 1) : Nonempty $ leftDescent w := by
  revert h
  have : (1 : G) ≠ 1 → Nonempty (leftDescent (1 : G)) := by
    intro h; contradiction
  refine OrderTwoGen.gen_induction_reduced_word_left (S := hG.S)
    (p := fun g ↦ g ≠ 1 → Nonempty (leftDescent g)) w this ?Hmul
  intro s L hr _ _
  use s
  simp only [leftDescent, leftAssocRefls, HOrderTwoGenGroup.length]
  refine And.intro (And.intro (SimpleRefl_is_Refl s.2) ?_) s.2
  nth_rw 1 [gprod_cons]
  rw [← mul_assoc, gen_square_eq_one' s, one_mul]
  have : reduced_word L := reduced_drop_of_reduced hr 1
  rw [← length_eq_iff.mp this, ← length_eq_iff.mp hr]
  simp

lemma rightDescent_NE_of_ne_one (h : w ≠ 1) : Nonempty $ rightDescent w := by
  rw [← inv_inv w, rightDescent_inv_eq_leftDescent]
  have : w⁻¹ ≠ 1 := by contrapose! h; exact inv_eq_one.mp h
  exact leftDescent_NE_of_ne_one this

lemma ne_one_of_length_smul_lt {s : hG.S} {w:G} (lt: ℓ(s*w) < ℓ(w)) : w ≠ 1 := by
  have : 0 < HOrderTwoGenGroup.length w := lt_of_le_of_lt (Nat.zero_le _) lt
  contrapose! this
  rw [HOrderTwoGenGroup.length]
  apply (length_zero_iff_one (S := hG.S)).mpr at this
  rw [this]

lemma length_smul_neq (s:hG.S) (w:G) : ℓ(s*w) ≠ ℓ(w) := by
  obtain ⟨L, hr, hL⟩ := @exists_reduced_word G _ hG.S _ w
  by_contra eq_len
  simp_rw [hL, HOrderTwoGenGroup.length] at eq_len
  obtain ⟨i, hi⟩ := hG.exchange hr (le_of_eq eq_len)
  rw [hi, ← length_eq_iff.mp hr] at eq_len
  linarith [List.removeNth_length L i,
    @length_le_list_length G _ hG.S _ (L.removeNth i)]


lemma length_muls (w : G) (s : hG.S) : OrderTwoGen.length hG.S (w * s) = OrderTwoGen.length hG.S (s * w⁻¹) := by
  nth_rw 1 [← inv_inv (w * s)]
  rw [mul_inv_rev, inv_length_eq_length]
  simp

lemma length_muls_neq (w:G) (s : hG.S) : ℓ(w * s) ≠ ℓ(w) := by
  simp only [HOrderTwoGenGroup.length]
  rw [length_muls w s, @length_eq_inv_length _ _ _ _ w]
  exact length_smul_neq s w⁻¹

lemma length_diff_one {s : hG.S} {g : G} : ℓ(s * g) = ℓ(g) + 1  ∨ ℓ(g) = ℓ(s*g) + 1 := by
  by_cases h : ℓ(s * g) ≤ ℓ(g)
  · apply fun h ↦ lt_of_le_of_ne h (length_smul_neq s g) at h
    simp only [HOrderTwoGenGroup.length] at *
    have := @length_le_length_smul_add_one _ _ _ _ g s
    apply Or.intro_right
    linarith
  · rw [not_le] at h
    simp only [HOrderTwoGenGroup.length] at *
    have := @length_smul_le_length_add_one _ _ _ _ g s
    apply Or.intro_left
    linarith

lemma length_smul_of_length_lt {s : hG.S} {w:G} (lt: ℓ(s * w) < ℓ(w)) : ℓ(s * w) = ℓ(w) - 1 := by
  rw [← Nat.succ_inj, Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.sub_add_cancel]
  . contrapose! lt
    symm at lt
    apply Or.resolve_right (length_diff_one) at lt
    linarith
  . linarith

lemma length_muls_of_length_lt {s : hG.S} {w:G} (lt: ℓ(w * s) < ℓ(w)) : ℓ(w * s) = ℓ(w) - 1 := by
  simp only [HOrderTwoGenGroup.length] at *
  rw [length_muls w s, @length_eq_inv_length _ _ _ _ w] at *
  repeat rw [← HOrderTwoGenGroup.length] at *
  exact length_smul_of_length_lt lt

lemma length_smul_of_length_gt {s : hG.S} {w:G} (gt: ℓ(w) < ℓ(s * w)) : ℓ(s * w) = ℓ(w) + 1 := by
  contrapose! gt
  apply Or.resolve_left (length_diff_one) at gt
  linarith

lemma length_muls_of_length_gt {s : hG.S} {w:G} (gt: ℓ(w) < ℓ(w * s)) : ℓ(w * s) = ℓ(w) + 1 := by
  simp only [HOrderTwoGenGroup.length] at *
  rw [length_muls w s, @length_eq_inv_length _ _ _ _ w] at *
  repeat rw [← HOrderTwoGenGroup.length] at *
  exact length_smul_of_length_gt gt

lemma length_muls_of_mem_leftDescent (s : leftDescent w) : ℓ(s*w) = ℓ(w) - 1 :=sorry

lemma length_muls_of_mem_rightDescent (s : rightDescent w) : ℓ(w*s) = ℓ(w) - 1 :=sorry

lemma muls_twice (w:G) (s:hG.S) : w*s*s = w := by
  rw [mul_assoc]
  by_cases h : s = (1 : G)
  . rw [h]; simp only [mul_one]
  . push_neg at h
    simp only [gen_square_eq_one', mul_one]

lemma smul_eq_muls_of_length_eq_pre (s t : hG.S) (w : G) :
  ℓ(s * w * t) = ℓ(w) ∧ ℓ(s * w) = ℓ(w * t) ∧ ℓ(s * w) > ℓ(w) → s * w = w * t := by
  obtain ⟨L, hr, hL⟩ := @exists_reduced_word G _ hG.S _ w
  intro h; rcases h with ⟨h₁, h₂, h₃⟩
  by_cases y : L = []
  . rw [y, gprod_nil] at hL
    rw [hL] at *
    simp only [reduced_word, mul_one, one_mul, gt_iff_lt] at *
    rw [HOrderTwoGenGroup.length, HOrderTwoGenGroup.length, length_of_one,
      length_zero_iff_one] at h₁
    rw [← mul_left_inj (t : G), gen_square_eq_one']
    exact h₁
  . push_neg at y
    have lt_len : ℓ(s * w * t) < ℓ(s * w) := by rw [h₁]; exact h₃
    have exch_prop: ∃ (i: Fin (s :: L).length), (s :: L : G) * t = (s :: L).removeNth i := by
      have : reduced_word (s :: L) := by
        apply length_eq_iff.2
        have : ℓ(s * w) = ℓ(w) + 1 := length_smul_of_length_gt h₃
        rw [hL, HOrderTwoGenGroup.length, HOrderTwoGenGroup.length,
            ← length_eq_iff.1, ← gprod_cons] at this
        apply this.symm
        apply hr
      rw [hL, HOrderTwoGenGroup.length, HOrderTwoGenGroup.length, ← gprod_cons] at lt_len
      rcases hG.exchange' this (Nat.le_of_lt lt_len) with ⟨i, j⟩
      use i
    rcases exch_prop with ⟨i, j⟩
    have exch_prop' : (s :: L : G) = ((s :: L).removeNth i) * t := by
      rw [← mul_left_inj (t : G), mul_assoc, gen_square_eq_one', mul_one]
      exact j
    have : i.1 = 0 := by
      by_contra x
      push_neg at x
      have i_pos : i.1 > 0 := Nat.pos_of_ne_zero x
      have : (L : G) * t = L.removeNth (i.1 - 1) := by
        rw [← one_mul (L : G), ← gen_square_eq_one' s, mul_assoc, mul_assoc]
        nth_rw 2 [← mul_assoc]
        rw [← gprod_cons, exch_prop', mul_assoc, gen_square_eq_one', mul_one, ← gprod_cons,
          List.removeNth_cons, gprod_cons, gprod_cons, ← mul_assoc, gen_square_eq_one', one_mul]
        exact i_pos
      have : ℓ((L : G) * t) < ℓ((L : G)) := by
        rw [this]
        nth_rw 2 [HOrderTwoGenGroup.length]
        rw [← length_eq_iff.1 (by exact hr)]
        have : (L.removeNth (i.1 - 1)).length = L.length - 1 := by
          rw [← add_left_inj 1, Nat.sub_add_cancel]
          apply List.removeNth_length L (⟨i.1 - 1, by exact Fin.subNat.proof_1 1 i i_pos⟩)
          apply List.length_pos.2 y
        have : ℓ((L.removeNth (i.1 - 1) : G)) ≤ L.length - 1 := by
          rw [← this]; apply length_le_list_length
        apply lt_of_le_of_lt this
        rw [← Nat.pred_eq_sub_one]
        apply Nat.pred_lt (ne_of_gt (List.length_pos.2 y))
      rw [hL] at *
      rw [← h₂] at this
      linarith
    rw [this, List.removeNth, gprod_cons, ← hL] at exch_prop'
    exact exch_prop'

lemma smul_eq_muls_of_length_eq (s t:hG.S) (w:G) :ℓ(s*w*t) = ℓ(w) ∧ ℓ(s*w)=ℓ(w*t) → s*w=w*t := by
  intro h; rcases h with ⟨h₁, h₂⟩
  by_cases k : ℓ(s * w) > ℓ(w)
  . apply smul_eq_muls_of_length_eq_pre
    constructor
    . exact h₁
    . constructor
      . exact h₂
      . exact k
  . push_neg at k
    have : ℓ(s * w) ≠ ℓ(w) := length_smul_neq s w
    have : ℓ(s * w) < ℓ(w) := by exact Nat.lt_of_le_of_ne k this
    nth_rw 2 [← one_mul w] at this
    rw [← gen_square_eq_one' s, mul_assoc] at this
    have : s * (s * w) = s * w * t := by
      apply smul_eq_muls_of_length_eq_pre s t (s * w)
      constructor
      . rw [← mul_assoc, gen_square_eq_one', one_mul]
        exact h₂.symm
      . constructor
        rw [← mul_assoc, gen_square_eq_one', one_mul]
        . exact h₁.symm
        . exact this
    rw [mul_assoc, mul_right_inj] at this
    exact this

lemma length_smul_eq_length_muls_of_length_neq (s t :hG.S) (w:G): ℓ(s*w*t) ≠ ℓ(w) → ℓ(s*w)=ℓ(w*t):= sorry

-- ℓ(s*w*t) = ℓ(w) or ℓ(s*w*t) = ℓ(w) + 2 or ℓ(s*w*t) = ℓ(w) - 2
-- ℓ(s*w*t) < ℓ(w) →  ℓ(s*w*t) < ℓ(s*w) <ℓ(w) ∧ ℓ(s*w*t) < ℓ(w*t) <ℓ(w)
lemma length_lt_of_length_smuls_lt {s t:hG.S} {w:G} (h: ℓ(s*w*t) < ℓ(w)) : ℓ(s*w*t) < ℓ(s*w) := sorry

lemma length_lt_of_length_smuls_lt' {s t:hG.S} {w:G} (h: ℓ(s*w*t) < ℓ(w)) : ℓ(s*w) < ℓ(w) := sorry

lemma length_gt_of_length_smuls_gt {s t:hG.S} {w:G} (h: ℓ(w) < ℓ(s*w*t)) : ℓ(w) < ℓ(s*w) :=sorry

lemma length_gt_of_length_smuls_gt' {s t:hG.S} {w:G} (h: ℓ(w) < ℓ(s*w*t)) : ℓ(s*w) <ℓ(s*w*t) :=sorry

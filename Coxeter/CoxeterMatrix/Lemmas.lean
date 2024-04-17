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
    have := @length_smul_le_length_add_one _ _ _ _ g s
    have := length_smul_neq s g
    apply Or.intro_left
    sorry --linarith
  · sorry

lemma length_smul_of_length_lt {s : hG.S} {w:G} (h : w ≠ 1) (lt: ℓ(s*w) < ℓ(w)) : ℓ(s*w) = ℓ(w) - 1 := sorry

lemma length_muls_of_length_lt {s : hG.S} {w:G} (h : w ≠ 1) (lt: ℓ(w*s) < ℓ(w)) : ℓ(w*s) = ℓ(w) - 1 := sorry

lemma length_smul_of_length_gt {s : hG.S} {w:G} (gt: ℓ(w) < ℓ(s*w)) : ℓ(s*w) = ℓ(w) + 1 := sorry

lemma length_muls_of_length_gt {s : hG.S} {w:G} (gt: ℓ(w) < ℓ(w*s)) : ℓ(w*s) = ℓ(w) + 1 := sorry

lemma length_muls_of_mem_leftDescent (s : leftDescent w) : ℓ(s*w) = ℓ(w) - 1 :=sorry

lemma length_muls_of_mem_rightDescent (s : rightDescent w) : ℓ(w*s) = ℓ(w) - 1 :=sorry

lemma muls_twice (w:G) (s:hG.S) : w*s*s = w := sorry

lemma smul_eq_muls_of_length_eq (s t:hG.S) (w:G) :ℓ(s*w*t) = ℓ(w) ∧ ℓ(s*w)=ℓ(w*t) → s*w=w*t:= sorry

lemma length_smul_eq_length_muls_of_length_neq (s t :hG.S) (w:G): ℓ(s*w*t) ≠ ℓ(w) → ℓ(s*w)=ℓ(w*t):= sorry

-- ℓ(s*w*t) = ℓ(w) or ℓ(s*w*t) = ℓ(w) + 2 or ℓ(s*w*t) = ℓ(w) - 2
-- ℓ(s*w*t) < ℓ(w) →  ℓ(s*w*t) < ℓ(s*w) <ℓ(w) ∧ ℓ(s*w*t) < ℓ(w*t) <ℓ(w)
lemma length_lt_of_length_smuls_lt {s t:hG.S} {w:G} (h: ℓ(s*w*t) < ℓ(w)) : ℓ(s*w*t) < ℓ(s*w) := sorry

lemma length_lt_of_length_smuls_lt' {s t:hG.S} {w:G} (h: ℓ(s*w*t) < ℓ(w)) : ℓ(s*w) < ℓ(w) := sorry

lemma length_gt_of_length_smuls_gt {s t:hG.S} {w:G} (h: ℓ(w) < ℓ(s*w*t)) : ℓ(w) < ℓ(s*w) :=sorry

lemma length_gt_of_length_smuls_gt' {s t:hG.S} {w:G} (h: ℓ(w) < ℓ(s*w*t)) : ℓ(s*w) <ℓ(s*w*t) :=sorry

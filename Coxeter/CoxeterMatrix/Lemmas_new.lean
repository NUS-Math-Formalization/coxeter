import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

import Coxeter.Aux_

variable {B : Type*}
variable {W : Type*}[Group W]
variable {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

variable {w : W} {i j : B}

namespace CoxeterSystem

local prefix:max "s" => cs.simple
local prefix:max "ℓ" => cs.length
local prefix:max "π" => cs.wordProd

-- lemma ne_one_of_length_smul_lt (lt : ℓ ((s i) * w) < ℓ w) : w ≠ 1 := by sorry

-- all descent lemmas are omitted

-- length_diff_one, length_smul/muls lemmas are omitted

lemma length_muls : ℓ (w * (s i)) = ℓ ((s i) * w⁻¹) := by
  nth_rw 1 [← inv_inv (w * (s i))]
  rw [mul_inv_rev, length_inv, inv_simple]

lemma length_smul_of_length_lt (lt : ℓ ((s i) * w) < ℓ w) : ℓ ((s i) * w) = ℓ w - 1 := by
  rw [← Nat.succ_inj, Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.sub_add_cancel]
  . contrapose! lt
    apply Or.resolve_right (length_simple_mul cs w i) at lt
    linarith
  . linarith

lemma length_muls_of_length_lt (lt : ℓ (w * (s i)) < ℓ w) : ℓ (w * (s i)) = ℓ w - 1 := by
  rw [length_muls] at *
  nth_rw 2 [← length_inv] at *
  exact length_smul_of_length_lt cs lt

lemma length_smul_of_length_gt (gt : ℓ w < ℓ ((s i) * w)) : ℓ ((s i) * w) = ℓ w + 1 := by
  contrapose! gt
  apply Or.resolve_left (length_simple_mul cs w i) at gt
  linarith

lemma length_muls_of_length_gt (gt : ℓ w < ℓ (w * (s i))) : ℓ (w * (s i)) = ℓ w + 1 := by
  rw [length_muls] at *
  nth_rw 1 [← length_inv] at gt
  nth_rw 2 [← length_inv]
  exact length_smul_of_length_gt cs gt

lemma length_smul_neq : ℓ ((s i) * w) ≠ ℓ w := by sorry

lemma length_muls_neq : ℓ (w * (s i)) ≠ ℓ w := by sorry

-- length_muls_of_mem_left/rightDescent omitted

-- muls_twice omitted: simple_mul_simple_cancel_right

lemma smul_eq_muls_of_length_eq_pre :
  ℓ ((s i) * w * (s j)) = ℓ w ∧ ℓ ((s i) * w) = ℓ (w * (s j)) ∧ ℓ ((s i) * w) > ℓ w
    → (s i) * w = w * (s j) := by
  obtain ⟨L, hr, hL⟩ := exists_reduced_word cs w
  intro h; rcases h with ⟨h₁, h₂, h₃⟩
  by_cases y : L = []
  . rw [y, wordProd_nil] at hL
    rw [hL] at *
    simp only [mul_one, length_one, length_eq_zero_iff, length_simple, one_mul, gt_iff_lt,
      zero_lt_one] at *
    rw [← mul_left_inj (s j), simple_mul_simple_self]
    exact h₁
  . push_neg at y
    have lt_len : ℓ ((s i) * w * (s j)) < ℓ ((s i) * w) := by rw [h₁]; exact h₃
    have exch_prop : ∃ (k : Fin (i :: L).length), (π (i :: L)) * (s j) = π ((i :: L).removeNth k) := by
      have : cs.IsReduced (i :: L) := by
        have : ℓ ((s i) * w) = ℓ w + 1 := by
          apply (not_isLeftDescent_iff cs w i).1
          simp only [IsLeftDescent]; push_neg; omega
        simp only [IsReduced]
        rw [wordProd_cons, ← hL, this]
        simp only [List.length_cons, Nat.succ.injEq]
        exact hr.symm
      rw [hL, ← wordProd_cons] at lt_len
      sorry -- exchange property here
    rcases exch_prop with ⟨k, l⟩
    have exch_prop' : (π (i :: L)) = π ((i :: L).removeNth k) * (s j) := by
      rw [← mul_left_inj (s j), mul_assoc, simple_mul_simple_self, mul_one]; exact l
    have : k.1 = 0 := by
      by_contra x
      push_neg at x
      have k_pos : k.1 > 0 := by omega
      have : w * (s j) = π (L.removeNth (k.1 - 1)) := by
        rw [← one_mul w, ← simple_mul_simple_self cs i, mul_assoc, mul_assoc]
        nth_rw 2 [← mul_assoc]
        rw [hL, ← wordProd_cons, exch_prop', mul_assoc, simple_mul_simple_self, mul_one,
          ← wordProd_cons, List.removeNth_cons, wordProd_cons, wordProd_cons, ← mul_assoc,
          simple_mul_simple_self, one_mul]
        exact k_pos
      have : ℓ (w * (s j)) < ℓ w := by
        rw [this, ← hr]
        have : (L.removeNth (k.1 - 1)).length = L.length - 1 := by
          rw [← add_left_inj 1, Nat.sub_add_cancel]
          apply List.removeNth_length L (⟨k.1 - 1, by exact Fin.subNat.proof_1 1 k k_pos⟩)
          apply List.length_pos.2 y
        have : ℓ (π (L.removeNth (k.1 - 1))) ≤ L.length - 1 := by
          rw [← this]; apply length_wordProd_le
        apply lt_of_le_of_lt this
        rw [← Nat.pred_eq_sub_one]
        apply Nat.pred_lt (ne_of_gt (List.length_pos.2 y))
      rw [hL] at *
      rw [← h₂] at this
      omega
    rw [this, List.removeNth, wordProd_cons, ← hL] at exch_prop'
    exact exch_prop'

lemma smul_eq_muls_of_length_eq :
  ℓ ((s i) * w * (s j)) = ℓ w ∧ ℓ ((s i) * w) = ℓ (w * (s j)) → (s i) * w = w * (s j) := by
  intro h; rcases h with ⟨h₁, h₂⟩
  by_cases k : ℓ ((s i) * w) > ℓ w
  . apply smul_eq_muls_of_length_eq_pre
    constructor
    . exact h₁
    . constructor
      . exact h₂
      . exact k
  . push_neg at k
    have : ℓ ((s i) * w) ≠ ℓ w := by sorry
    have : ℓ ((s i) * w) < ℓ w := by omega
    nth_rw 2 [← one_mul w] at this
    rw [← simple_mul_simple_self cs i, mul_assoc] at this
    have : (s i) * ((s i) * w) = (s i) * w * (s j) := by
      apply smul_eq_muls_of_length_eq_pre
      constructor
      . simp only [simple_mul_simple_cancel_left]; exact h₂.symm
      . constructor
        . simp only [simple_mul_simple_cancel_left]; exact h₁.symm
        . exact this
    rw [mul_assoc, mul_right_inj] at this; exact this

lemma length_smul_muls :
  ℓ ((s i) * w * (s j)) = ℓ w ∨ ℓ ((s i) * w * (s j)) = ℓ w + 2
    ∨ ℓ ((s i) * w * (s j)) + 2 = ℓ w := by
  by_cases h : ℓ ((s i) * w) = ℓ w + 1
  . by_cases h' : ℓ ((s i) * w * (s j)) = ℓ ((s i) * w) + 1
    . right; left; omega
    . have : ℓ ((s i) * w * (s j)) + 1 = ℓ ((s i) * w) :=
        (Or.resolve_left (length_mul_simple cs ((s i) * w) j)) h'
      left; omega
  . have : ℓ ((s i) * w) + 1 = ℓ w := (Or.resolve_left (length_simple_mul cs w i)) h
    by_cases h' : ℓ ((s i) * w * (s j)) = ℓ ((s i) * w) + 1
    . left; omega
    . have : ℓ ((s i) * w * (s j)) + 1 = ℓ ((s i) * w) :=
        (Or.resolve_left (length_mul_simple cs ((s i) * w) j)) h'
      right; right; omega

lemma length_smul_eq_length_muls_of_length_neq_pre :
  ℓ ((s i) * w * (s j)) = ℓ w + 2 → ℓ ((s i) * w) = ℓ (w * (s j)) := by
  intro h
  have : ℓ ((s i) * w) = ℓ w + 1 := by
    by_contra h'
    have : ℓ ((s i) * w) + 1 = ℓ w := (Or.resolve_left (length_simple_mul cs w i)) h'
    rcases (length_mul_simple cs ((s i) * w) j) with h₁ | h₂
    . omega
    . omega
  have : ℓ (w * (s j)) = ℓ w + 1 := by
    by_contra h'
    have : ℓ (w * (s j)) + 1 = ℓ w := (Or.resolve_left (length_mul_simple cs w j)) h'
    have : ℓ ((s i) * (w * (s j))) = ℓ (w * (s j)) + 1 ∨ ℓ ((s i) * (w * (s j))) + 1 = ℓ (w * (s j)) :=
      length_simple_mul cs (w * (s j)) i
    rw [← mul_assoc] at this
    rcases this with h₁ | h₂
    . rw [this, h] at h₁
      omega
    . rw [← add_left_inj 1, this, ← add_left_inj 2, ← h, add_assoc, add_assoc] at h₂
      simp only [Nat.reduceAdd, add_right_eq_self, OfNat.ofNat_ne_zero] at h₂
  omega

lemma length_smul_eq_length_muls_of_length_neq :
  ℓ ((s i) * w * (s j)) ≠ ℓ w → ℓ ((s i) * w) = ℓ (w * (s j)) := by
  intro h
  rcases ((Or.resolve_left (length_smul_muls cs)) h) with h₁ | h₂
  . apply length_smul_eq_length_muls_of_length_neq_pre cs h₁
  . apply Eq.symm
    nth_rw 1 [← one_mul w, ← simple_mul_simple_self cs i]
    simp_rw [mul_assoc]
    nth_rw 2 [← mul_assoc, ← mul_one w]
    rw [← simple_mul_simple_self cs j]
    nth_rw 3 [← mul_assoc]
    nth_rw 2 [← mul_assoc, ← mul_assoc]
    apply length_smul_eq_length_muls_of_length_neq_pre
    rw [← mul_assoc]
    simp only [simple_mul_simple_cancel_left, simple_mul_simple_cancel_right]
    exact h₂.symm

lemma length_lt_of_length_smuls_lt (h : ℓ ((s i) * w * (s j)) < ℓ w) :
  ℓ ((s i) * w * (s j)) < ℓ ((s i) * w) := by
  have : ℓ ((s i) * w * (s j)) + 2 = ℓ w := by
    have : ℓ ((s i) * w * (s j)) = ℓ w + 2 ∨ ℓ ((s i) * w * (s j)) + 2 = ℓ w := by
      exact (length_smul_muls cs).resolve_left (by linarith)
    exact this.resolve_left (by omega)
  rcases (length_simple_mul cs w i) with h₁ | h₂
  . omega
  . omega

lemma length_lt_of_length_smuls_lt' (h : ℓ ((s i) * w * (s j)) < ℓ w) :
  ℓ ((s i) * w) < ℓ w := by
  have : ℓ ((s i) * w * (s j)) + 2 = ℓ w := by
    have : ℓ ((s i) * w * (s j)) = ℓ w + 2 ∨ ℓ ((s i) * w * (s j)) + 2 = ℓ w := by
      exact (length_smul_muls cs).resolve_left (by linarith)
    exact this.resolve_left (by omega)
  have : ℓ ((s i) * w) + 1 = ℓ w := by
    by_contra h'
    have : ℓ ((s i) * w) = ℓ w + 1 := (Or.resolve_right (length_simple_mul cs w i)) h'
    rcases (length_mul_simple cs ((s i) * w) j) with h₁ | h₂
    . omega
    . omega
  . omega

lemma length_gt_of_length_smuls_gt (h : ℓ w < ℓ ((s i) * w * (s j))) :
  ℓ w < ℓ ((s i) * w) := by
  have : ℓ ((s i) * w * (s j)) = ℓ w + 2 := by
    have : ℓ ((s i) * w * (s j)) = ℓ w + 2 ∨ ℓ ((s i) * w * (s j)) + 2 = ℓ w := by
      apply (length_smul_muls cs).resolve_left (by linarith)
    exact this.resolve_right (by omega)
  have : ℓ ((s i) * w) = ℓ w + 1 := by
    by_contra h'
    have : ℓ ((s i) * w) + 1 = ℓ w := (Or.resolve_left (length_simple_mul cs w i)) h'
    rcases (length_mul_simple cs ((s i) * w) j) with h₁ | h₂
    . omega
    . omega
  omega


lemma length_gt_of_length_smuls_gt' (h : ℓ w < ℓ ((s i) * w * (s j))) :
  ℓ w < ℓ ((s i) * w * (s j)) := by
  have : ℓ ((s i) * w * (s j)) = ℓ w + 2 := by
    have : ℓ ((s i) * w * (s j)) = ℓ w + 2 ∨ ℓ ((s i) * w * (s j)) + 2 = ℓ w := by
      apply (length_smul_muls cs).resolve_left (by linarith)
    exact this.resolve_right (by omega)
  omega

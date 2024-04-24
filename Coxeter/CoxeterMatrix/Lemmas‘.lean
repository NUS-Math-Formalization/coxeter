import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

import Coxeter.Aux_
import Coxeter.CoxeterMatrix.Characterization'

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
open CoxeterGroup

lemma length_smul_neq : ℓ ((s i) * w) ≠ ℓ w := by
  by_contra h
  have := length_mul_mod_two cs (s i) w
  rw [h, length_simple] at this
  omega

lemma length_muls_neq : ℓ (w * (s i)) ≠ ℓ w := by
  by_contra h
  have := length_mul_mod_two cs w (s i)
  rw [h, length_simple] at this
  omega

-- length_muls_of_mem_left/rightDescent omitted

-- muls_twice omitted: simple_mul_simple_cancel_right

-- the following lemma is to be moved to aux_ once the file is ready
lemma eraseIdx_length (L : List B) (k : ℕ) (h : k < L.length) : (L.eraseIdx k).length = L.length - 1 := by
  induction L generalizing k with
  | nil =>
    simp only [List.eraseIdx_nil, List.length_nil, ge_iff_le, zero_le, tsub_eq_zero_of_le]
  | cons hd tail ih =>
    simp only [List.length_cons, Nat.succ_sub_succ_eq_sub, tsub_zero]
    by_cases l : k = 0
    . rw [l]; simp only [List.eraseIdx_cons_zero]
    . have k_pos := Nat.pos_of_ne_zero l
      rw [← Nat.sub_add_cancel k_pos]
      simp only [Nat.reduceSucc, List.eraseIdx_cons_succ, List.length_cons]
      rw [Nat.succ_eq_add_one]
      have : k - 1 < tail.length := by rw [List.length_cons] at h; omega
      have tlen_pos : 0 < tail.length := by omega
      rw [← Nat.sub_add_cancel tlen_pos]
      simp only [Nat.reduceSucc, add_left_inj]
      apply ih
      apply this

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
    have exch_prop : ∃ k < (i :: L).length, (π (i :: L)) * (s j) = π ((i :: L).eraseIdx k) := by
      apply right_exchange'
      simp only [IsRightInversion]
      constructor
      . simp only [IsReflection]
        use 1, j; simp only [one_mul, inv_one, mul_one]
      . rw [wordProd_cons, ← hL]
        exact lt_len
    rcases exch_prop with ⟨k, ⟨l₁, l₂⟩⟩
    have exch_prop' : (π (i :: L)) = π ((i :: L).eraseIdx k) * (s j) := by
      rw [← mul_left_inj (s j), simple_mul_simple_cancel_right]
      exact l₂
    have : k = 0 := by
      by_contra x
      push_neg at x
      have k_pos : k > 0 := Nat.pos_of_ne_zero x
      have : (π L) * (s j) = π (L.eraseIdx (k - 1)) := by
        rw [← one_mul (π L), ← simple_mul_simple_self cs i, mul_assoc, mul_assoc]
        nth_rw 2 [← mul_assoc]
        rw [← wordProd_cons, exch_prop', simple_mul_simple_cancel_right]
        nth_rw 1 [← Nat.sub_add_cancel k_pos]
        simp only [Nat.reduceSucc, List.eraseIdx_cons_succ, wordProd_cons,
          simple_mul_simple_cancel_left]
      have : ℓ ((π L) * (s j)) < ℓ (π L) := by
        rw [this, ← hL, ← hr]
        have erase_len : (L.eraseIdx (k - 1)).length = L.length - 1 := by
          apply eraseIdx_length
          rw [List.length_cons] at l₁
          omega
        have := length_wordProd_le cs (L.eraseIdx (k - 1))
        apply lt_of_le_of_lt this
        rw [erase_len]
        apply Nat.pred_lt (ne_of_gt (List.length_pos.2 y))
      rw [← hL, ← h₂] at this
      linarith
    rw [this, List.eraseIdx_cons_zero, wordProd_cons, ← hL] at exch_prop'
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
    have : ℓ ((s i) * w) ≠ ℓ w := length_smul_neq cs
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

lemma length_smul_muls_imp_smul : ℓ ((s i) * w * (s j)) = ℓ w + 2 → ℓ ((s i) * w) = ℓ w + 1 := by
  intro h
  by_contra h'
  have : ℓ ((s i) * w) + 1 = ℓ w := (Or.resolve_left (length_simple_mul cs w i)) h'
  rcases (length_mul_simple cs ((s i) * w) j) with h₁ | h₂
  . omega
  . omega

lemma length_smul_muls_imp_muls : ℓ ((s i) * w * (s j)) = ℓ w + 2 → ℓ (w * (s j)) = ℓ w + 1 := by
  intro h
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

lemma length_smul_eq_length_muls_of_length_neq_pre :
  ℓ ((s i) * w * (s j)) = ℓ w + 2 → ℓ ((s i) * w) = ℓ (w * (s j)) := by
  intro h; linarith [(length_smul_muls_imp_smul cs h), (length_smul_muls_imp_muls cs h)]

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
    have := (length_smul_muls cs).resolve_left (by linarith)
    exact this.resolve_left (by omega)
  rcases (length_simple_mul cs w i) with h₁ | h₂
  . omega
  . omega

lemma length_lt_of_length_smuls_lt' (h : ℓ ((s i) * w * (s j)) < ℓ w) :
  ℓ ((s i) * w) < ℓ w := by
  have : ℓ ((s i) * w * (s j)) + 2 = ℓ w := by
    have := (length_smul_muls cs).resolve_left (by linarith)
    exact this.resolve_left (by omega)
  have : ℓ ((s i) * w) + 1 = ℓ w := by
    by_contra h'
    have := (Or.resolve_right (length_simple_mul cs w i)) h'
    rcases (length_mul_simple cs ((s i) * w) j) with h₁ | h₂
    . omega
    . omega
  omega

lemma length_gt_of_length_smuls_gt (h : ℓ w < ℓ ((s i) * w * (s j))) :
  ℓ w < ℓ ((s i) * w) := by
  have : ℓ ((s i) * w * (s j)) = ℓ w + 2 := by
    have := (length_smul_muls cs).resolve_left (by linarith)
    exact this.resolve_right (by omega)
  linarith [length_smul_muls_imp_smul cs this]


lemma length_gt_of_length_smuls_gt' (h : ℓ w < ℓ ((s i) * w * (s j))) :
  ℓ w < ℓ ((s i) * w * (s j)) := by
  have : ℓ ((s i) * w * (s j)) = ℓ w + 2 := by
    have := (length_smul_muls cs).resolve_left (by linarith)
    exact this.resolve_right (by omega)
  omega

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length

variable {B : Type*}
variable {W : Type*}[Group W]
variable {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

variable {w : W} {i j : B}

namespace CoxeterSystem

local prefix:max "s" => cs.simple
local prefix:max "ℓ" => cs.length

lemma ne_one_of_length_smul_lt (lt : ℓ ((s i) * w) < ℓ w) : w ≠ 1 := by sorry

-- all descent lemmas are omitted

-- length_diff_one, length_smul/muls lemmas are omitted

lemma length_smul_of_length_lt (lt : ℓ ((s i) * w) < ℓ w) : ℓ ((s i) * w) = ℓ w - 1 := by sorry

lemma length_muls_of_length_lt (lt : ℓ (w * (s i)) < ℓ w) : ℓ (w * (s i)) = ℓ w - 1 := by sorry

lemma length_smul_of_length_gt (gt : ℓ w < ℓ ((s i) * w)) : ℓ ((s i) * w) = ℓ w + 1 := by sorry

lemma length_muls_of_length_gt (gt : ℓ w < ℓ (w * (s i))) : ℓ (w * (s i)) = ℓ w + 1 := by sorry

lemma length_muls_of_mem_leftDescent (h : cs.IsLeftDescent w i) : ℓ ((s i) * w) < ℓ w := by sorry

lemma length_muls_of_mem_rightDescent (h : cs.IsRightDescent w i) : ℓ (w * (s i)) < ℓ w := by sorry

-- errr why is this here...????
lemma muls_twice : w * (s i) * (s i) = w := by sorry

lemma smul_eq_muls_of_length_eq_pre :
  ℓ ((s i) * w * (s j)) = ℓ w ∧ ℓ ((s i) * w) = ℓ (w * (s j)) ∧ ℓ ((s i) * w) > ℓ w
    → (s i) * w = w * (s j) := by sorry

lemma smul_eq_muls_of_length_eq :
  ℓ ((s i) * w * (s j)) = ℓ w ∧ ℓ ((s i) * w) = ℓ (w * (s j)) → (s i) * w = w * (s j) := by sorry

lemma length_siwsj :
  ℓ ((s i) * w * (s j)) = ℓ w ∨ ℓ ((s i) * w * (s j)) = ℓ w + 2
    ∨ ℓ w = ℓ ((s i) * w * (s j)) + 2 := by sorry

lemma length_smul_eq_length_muls_of_length_neq_pre :
  ℓ ((s i) * w * (s j)) = ℓ w + 2 → ℓ ((s i) * w) = ℓ ((s j) * w) := by sorry

lemma length_smul_eq_length_muls_of_length_neq :
  ℓ ((s i) * w * (s j)) ≠ ℓ w → ℓ ((s i) * w) = ℓ ((s j) * w) := by sorry

lemma length_lt_of_length_smuls_lt (h : ℓ ((s i) * w * (s j)) < ℓ w) :
  ℓ ((s i) * w * (s j)) < ℓ ((s i) * w) := by sorry

lemma length_lt_of_length_smuls_lt' (h : ℓ ((s i) * w * (s j)) < ℓ w) :
  ℓ ((s i) * w) < ℓ w := by sorry

lemma length_gt_of_length_smuls_gt (h : ℓ w < ℓ ((s i) * w * (s j))) :
  ℓ w < ℓ ((s i) * w) := by sorry

lemma length_gt_of_length_smuls_gt' (h : ℓ w < ℓ ((s i) * w * (s j))) :
  ℓ w < ℓ ((s i) * w * (s j)) := by sorry

import Coxeter.OrderTwoGen
import Coxeter.Aux_
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Inversion

/-!
# A Characterization

In this file we define the `ExchangeProp` and `DeletionProp` for an `OrderTwoGen` group `G`.
We then prove that they are equivalent.
-/

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs: CoxeterSystem M W)

local prefix:max "s" => cs.simple
local prefix:max "ℓ" => cs.length
local prefix:max "ris" => cs.rightInvSeq
local prefix:max "π" => cs.wordProd

namespace CoxeterGroup

/-- Exchange Property:
Given an `OrderTwoGen` group, we say the system satisfy the Exchange Property if
given a reduced expression `w = s₁ s₂ ⋯ sₙ ∈ G` and `s ∈ S`,
there exists `1 ≤ i < n` such that `s s₁ ⋯ sₙ = s₁ ⋯ sᵢ₋₁ sᵢ₊₁ ⋯ sₙ` -/
theorem right_exchange {ω : List B} {t : W} (h : cs.IsRightInversion (π ω) t) : t ∈ cs.rightInvSeq ω := sorry

/-- Mirrored version of Exchange Property -/
theorem left_exchange {ω : List B} {t : W} (h : cs.IsLeftInversion (π ω) t) : t ∈ cs.leftInvSeq ω := sorry

theorem right_exchange' {ω : List B} {t : W} (h : cs.IsRightInversion (π ω) t) : ∃ j < ω.length, π ω * t = π (ω.eraseIdx j) := sorry

theorem left_exchange' {ω : List B} {t : W} (h : cs.IsLeftInversion (π ω) t) : ∃ j < ω.length, t * π ω = π (ω.eraseIdx j) := sorry

/-- Deletion Property:
Given an `OrderTwoGen` group, we say the system satisfy the deletion property if
given an expression `w = s₁ s₂ ⋯ sₙ ∈ G`, there exists `1 ≤ i, j < n` such that
`w = s₁ ⋯ sᵢ₋₁ sᵢ₊₁ ⋯ sⱼ₋₁ sⱼ₋₁ ⋯ sₙ` -/
def non_reduced_p (ω : List B) := fun k => ¬cs.IsReduced (ω.drop k)

lemma max_non_reduced_word_index_aux (ω : List B) (hω : ¬cs.IsReduced ω) :
  ∃ n, non_reduced_p cs ω n := by
  use 0
  rw [non_reduced_p, List.drop_zero]
  exact hω

noncomputable def max_non_reduced_word_index (ω : List B) :=
  @Nat.findGreatest (non_reduced_p cs ω) (Classical.decPred _) (ω.length)

lemma empty_is_reduced : cs.IsReduced [] := by
  show ℓ (π []) = [].length
  simp only [CoxeterSystem.wordProd_nil, CoxeterSystem.length_one, List.length_nil]

private lemma not_reduced_imp_not_empty (ω : List B) (h : ¬cs.IsReduced ω) : ω ≠ [] := by
  by_contra!
  rw [this] at h
  have := empty_is_reduced cs
  contradiction

private lemma max_index_is_not_reduced (ω : List B) (i : ℕ) (h₀ : ¬cs.IsReduced ω)
  (h₁ : i = max_non_reduced_word_index cs ω) : ¬cs.IsReduced (ω.drop i) := by
  rw [← non_reduced_p]
  by_cases h : i = 0
  . rw [h, non_reduced_p, List.drop_zero]; exact h₀
  . apply @Nat.findGreatest_of_ne_zero i (non_reduced_p cs ω) (Classical.decPred _) (ω.length)
    . rw [max_non_reduced_word_index] at h₁; exact h₁.symm
    . exact h

private lemma beyond_max_index_is_reduced (ω : List B) (n : ℕ) (h₀ : n ≤ ω.length)
  (h₁ : n > max_non_reduced_word_index cs ω) : cs.IsReduced (ω.drop n) := by
  apply of_not_not
  simp only [max_non_reduced_word_index] at h₁
  apply @Nat.findGreatest_is_greatest n (non_reduced_p cs ω) (Classical.decPred _) (ω.length)
  exact h₁; exact h₀

private lemma max_index_lt_length (ω : List B) (i : ℕ) (h : i = max_non_reduced_word_index cs ω)
  (hω : ¬cs.IsReduced ω) : i < ω.length := by
  have ω_not_empty : ω ≠ [] := by
    by_contra!
    rw [this] at hω
    have := empty_is_reduced cs
    contradiction
  have := @Nat.findGreatest_le (non_reduced_p cs ω) (Classical.decPred _) (List.length ω)
  have i_ne_len : i ≠ ω.length := by
    simp only [max_non_reduced_word_index] at h
    by_contra!
    rw [h] at this
    have : ¬cs.IsReduced (ω.drop ω.length) := by
      rw [← non_reduced_p]
      apply @Nat.findGreatest_of_ne_zero (ω.length) (non_reduced_p cs ω) (Classical.decPred _)
      apply this
      have := List.length_pos.2 ω_not_empty
      omega
    simp only [List.drop_length] at this
    have := empty_is_reduced cs
    contradiction
  rw [h, max_non_reduced_word_index] at *
  exact Nat.lt_of_le_of_ne this i_ne_len

theorem DeletionProp (ω : List B) (hω : ¬cs.IsReduced ω) : ∃ j < ω.length, ∃ i < j, π ω = π ((ω.eraseIdx i).eraseIdx j) := by
  have ω_not_empty := not_reduced_imp_not_empty cs ω hω
  let i := max_non_reduced_word_index cs ω
  have := max_index_lt_length cs ω i rfl hω
  let ω1 := ω.drop i; let ω2 := ω.drop (i + 1)
  have : ω1 ≠ [] := by
    simp only [ω1]
    apply List.length_pos.1
    rw [List.length_drop]
    omega
  let si := ω1.head this
  have := max_index_is_not_reduced cs ω i hω rfl
  have ω2_reduced : cs.IsReduced ω2 := by apply beyond_max_index_is_reduced; omega; omega
  have : ℓ (π ω1) < ℓ (π ω2) := by
    have := (List.tail_drop ω i).symm
    have hd_tail : ω1 = si :: ω2 := by
      simp only [ω1, ω2, si]; rw [this]; simp only [List.head_cons_tail]
    rw [hd_tail, CoxeterSystem.wordProd_cons]
    by_contra!
    have : ℓ ((s si) * (π ω2)) = ℓ (π ω2) + 1 := by
      apply (CoxeterSystem.length_simple_mul cs (π ω2) si).resolve_right; omega
    have : cs.IsReduced ω1 := by
      show ℓ (π ω1) = ω1.length
      rw [hd_tail, CoxeterSystem.wordProd_cons, List.length_cons, Nat.succ_eq_add_one, this]
      simp only [add_left_inj]
      exact ω2_reduced
    contradiction
  have exch_prop : ∃ j < ω.length - i, π ω1 = π (ω2.eraseIdx j) := by sorry
  sorry

/-
/-! ### The exchange properties and deletion property -/

/-- The right exchange property:
Let $w = s_{i_1} \cdots s_{i_\ell}$ be a reduced expression for an element $w \in W$
and let $t \in W$.
The following are equivalent:
* $t$ is a right inversion of $w$.
* $t$ appears in the right inversion sequence of the word $s_{i_1} \cdots s_{i_\ell}$.
* There exists $j$ with $1 \leq j \leq \ell$ such that
  $$wt = s_{i_1} \cdots \widehat{s_{i_j}} \cdots s_{i_\ell}$$
  (i.e. the result of multiplying all of the simple reflections $s_{i_1}, \ldots, s_{i_\ell}$
  except $s_{i_j}$).
-/
theorem right_exchange_tfae_of_reduced {ω : List B} (t : W) (rω : cs.IsReduced ω) :
    List.TFAE [
      cs.IsRightInversion (π ω) t,
      t ∈ ris ω,
      ∃ j < ω.length, (π ω) * t = π (ω.eraseIdx j)
    ] := by
  sorry

/-- The left exchange property:
Let $w = s_{i_1} \cdots s_{i_\ell}$ be a reduced expression for an element $w \in W$
and let $t \in W$.
The following are equivalent:
* $t$ is a left inversion of $w$.
* $t$ appears in the left inversion sequence of the word $s_{i_1} \cdots s_{i_\ell}$.
* There exists $j$ with $1 \leq j \leq \ell$ such that
  $$tw = s_{i_1} \cdots \widehat{s_{i_j}} \cdots s_{i_\ell}$$
  (i.e. the result of multiplying all of the simple reflections $s_{i_1}, \ldots, s_{i_\ell}$
  except $s_{i_j}$).
-/
theorem left_exchange_tfae_of_reduced {ω : List B} (t : W) (rω : cs.IsReduced ω) :
    List.TFAE [
      cs.IsLeftInversion (π ω) t,
      t ∈ lis ω,
      ∃ j < ω.length, t * (π ω) = π (ω.eraseIdx j)
    ] := by
  sorry

theorem nodup_rightInvSeq_iff (ω : List B) :
    List.Nodup (ris ω) ↔ cs.IsReduced ω := by
  sorry

theorem nodup_leftInvSeq_iff (ω : List B) :
    List.Nodup (lis ω) ↔ cs.IsReduced ω := by
  sorry

-/

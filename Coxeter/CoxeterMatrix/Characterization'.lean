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

/-
namespace OrderTwoGen
variable {G : Type*} [Group G] (S : Set G) [OrderTwoGen S]

local notation : max "ℓ(" g ")" => (length S g)
-/
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

theorem DeletionProp (ω : List B) (hω : ¬cs.IsReduced ω) : ∃ j < ω.length, ∃ i < j, π ω = π ((ω.eraseIdx j).eraseIdx i) := by
  have ω_not_empty : ω ≠ [] := by
    by_contra!
    rw [this] at hω
    have := empty_is_reduced cs
    contradiction
  let j := max_non_reduced_word_index cs ω; use j
  have : j ≤ ω.length := by
    simp only [j, max_non_reduced_word_index]
    exact @Nat.findGreatest_le (non_reduced_p cs ω) (Classical.decPred _) (List.length ω)
  have : j ≠ ω.length := by
    simp only [j, max_non_reduced_word_index]
    by_contra!
    have : ¬cs.IsReduced (ω.drop ω.length) := by
      rw [← non_reduced_p]
      apply @Nat.findGreatest_of_ne_zero (ω.length) (non_reduced_p cs ω) (Classical.decPred _)
      apply this
      have := List.length_pos.2 ω_not_empty
      omega
    simp only [List.drop_length] at this
    have := empty_is_reduced cs
    contradiction
  let ω1 := ω.take j
  let s1 := ω.get ⟨j, sorry⟩

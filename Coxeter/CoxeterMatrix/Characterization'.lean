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
theorem DeletionProp (ω : List B) (hω : ¬ cs.IsReduced ω) : ∃ j < ω.length, ∃ i < j, π ω = π ((ω.eraseIdx j).eraseIdx i) := sorry

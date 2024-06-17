import Mathlib.Init.Order.Defs
import Mathlib.Data.Fintype.Basic

namespace PartialOrder
variable {P : Type*} [PartialOrder P] [Fintype P]

lemma split_tail (L : List P) (n : Fin L.length) (h₀ : n.1 > 0) (h₁ : L.take n ≠ []) : L[n.1-1] = (L.take n).getLast h₁ := by
  have len : (L.take n).length = n := by simp
  sorry

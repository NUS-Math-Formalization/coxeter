import Coxeter.ForMathlib.PosetChain

open PartialOrder
/-
Definition: A finite poset P is called graded if it is pure and bounded.
A poset is called pure if all maximal chains are of the same length.
-/
class GradedPoset (P : Type*) [PartialOrder P][Fintype P] extends BoundedOrder P where
  pure: ∀ (L₁ L₂ : List P), ((maximal_chain L₁) ∧ (maximal_chain L₂)) → (L₁.length = L₂.length)

namespace GradedPoset
/-
Definition/Lemma : The corank of a graded poset is the length of any maximal chain in P.
-/

lemma rank_def  {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P]: ∀ L ∈ maximalChains P, rank P = L.length := by
  intro L hL
  simp [rank, maximalChains] at *
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro L' hL'
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hL'
    rw [pure L L' ⟨hL, hL'⟩]
  · apply Finset.le_sup
    simp only [Set.mem_toFinset, Set.mem_setOf_eq]
    exact hL

end GradedPoset

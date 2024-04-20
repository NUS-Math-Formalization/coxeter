import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Coxeter.ForMathlib.AbstractSimplicialComplex
import Coxeter.ForMathlib.PosetChain
import Coxeter.ForMathlib.PosetGraded
import Mathlib.Data.Finset.Sort

noncomputable section
open Classical

namespace PartialOrder

open AbstractSimplicialComplex

variable {P : Type*} [PartialOrder P] --[Fintype P] [GradedPoset P]

/-
Definition: Let P be a poset. Let Delta(P) be the set of all chains in P.
Note that each element in Delta(P) will considered as a chain.
-/
@[simp]
def Delta_List (P : Type*) [PartialOrder P] : Set (List P) := {L : List P | chain L}

@[simp]
abbrev Delta (P : Type*) [PartialOrder P] : AbstractSimplicialComplex P where
  faces := List.toFinset '' Delta_List P
  empty_mem := by simp
  lower' := by
    simp only [IsLowerSet]
    intro a b blea ain
    simp only [Delta_List, Set.mem_image, Set.mem_setOf_eq]
    simp at ain
    rcases ain with ⟨al, chain_a, ha⟩
    use List.filter (· ∈ b) al
    simp only [List.toFinset_filter, decide_eq_true_eq]
    constructor
    · simp [chain]
      exact List.Chain'.sublist chain_a (List.filter_sublist al)
    · rw [ha]
      simp at blea
      ext x
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      intro hb
      exact blea hb




/-
Definition: Let P be a graded poset. Then Delta.ASC (P) is a pure abstract simplicial complex.
-/
instance Delta.Pure {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P]: Pure (Delta P) where
  pure := by
    intro s sin t tin
    have := GradedPoset.pure (P := P)
    simp only [Facets, IsFacet] at *
    sorry





end PartialOrder

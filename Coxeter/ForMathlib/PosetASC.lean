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

/-
Definition: Let P be a poset. Delta P is the set of all chains in P, which is an abstract simplicial complex.
Note that each element in Delta (P) will considered as a subset of P.
-/
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


lemma List.sub_toFinset_of_sublist {L₁ L₂ : List P} : L₂.Sublist L₁ → L₂.toFinset ⊆ L₁.toFinset := by
  intro sublst
  intro x hx
  simp at hx
  have := List.Sublist.subset sublst
  have : x ∈ L₁ := this hx
  simp [this]

/-
Definition: Let P be a graded poset. Then Delta.ASC (P) is a pure abstract simplicial complex.
-/
instance Delta.Pure {P : Type*} [PartialOrder P] [Fintype P] [GradedPoset P]: Pure (Delta P) where
  pure := by
    rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
    have := GradedPoset.pure (P := P)
    simp [Facets, IsFacet, Delta, mem_faces.symm] at *
    rcases hs₁ with ⟨L₁, chain_l₁, seq⟩
    rcases ht₁ with ⟨L₂, chain_l₂, teq⟩
    subst seq teq
    rw [List.toFinset_card_of_nodup (chain_nodup chain_l₁), List.toFinset_card_of_nodup (chain_nodup chain_l₂)]
    refine this _ _ chain_l₁ ?_ chain_l₂ ?_
    · intro L' chain_l' sublst
      apply List.Sublist.eq_of_length sublst
      rw [← List.toFinset_card_of_nodup (chain_nodup chain_l₁), ← List.toFinset_card_of_nodup (chain_nodup chain_l')]
      have := hs₂ L' chain_l' (List.sub_toFinset_of_sublist sublst)
      simp [this]
    · intro L' chain_l' sublst
      apply List.Sublist.eq_of_length sublst
      rw [← List.toFinset_card_of_nodup (chain_nodup chain_l₂), ← List.toFinset_card_of_nodup (chain_nodup chain_l')]
      have := ht₂ L' chain_l' (List.sub_toFinset_of_sublist sublst)
      simp [this]





end PartialOrder

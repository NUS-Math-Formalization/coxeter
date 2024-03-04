import Coxeter.CoxeterSystem

import Mathlib.Data.Set.Card

namespace Shelling

variable {P : Type*} [PartialOrder P] [Finite P]

def ledot (a b : P) := a < b ∧ (∀ {c : P}, (a ≤ c ∧ c ≤ b) → (a = c ∨ b = c))

def edges {P : Type*} [PartialOrder P] : Set (P × P) := { (a, b) | ledot a b }

def EL {P A : Type*} [PartialOrder P] [PartialOrder A] := edges P → A

def maximal_chain {P : Type*} [PartialOrder P] : List P := sorry

def graded {P : Type*} [PartialOrder P] : ∀ (L₁ L₂ : List P), ((maximal_chain L₁) ∧ (maximal_chain L₂)) → (L₁.length = L₂.length)

def shellable {P : Type*} [PartialOrder P] : sorry

def CL_labelling {P : Type*} [PartialOrder P] : sorry

def EL_labelling {P : Type*} [PartialOrder P] : sorry

theorem CL_shellable {P : Type*} [PartialOrder P] (h: CL_labelling P) : shellable P := by sorry

theorem EL_CL {P : Type*} [PartialOrder P] (h: EL_labelling P) : CL_labelling P := by sorry

theorem EL_shellable {P : Type*} [PartialOrder P] (h: EL_labelling P) : shellable P := by
  apply EL_CL at h
  apply CL_shellable h

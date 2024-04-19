import Coxeter.CoxeterMatrix.CoxeterMatrix
import Coxeter.StrongExchange
import Coxeter.BruhatOrder
import Coxeter.ForMathlib.ELlabeling

import Mathlib.Data.Set.Card

open HOrderTwoGenGroup CoxeterMatrix CoxeterGroup PartialOrder AlternatingWord

open Bruhat

open Classical

variable {G} [cox : CoxeterGroup G]

namespace ReflectionOrder
#check LinearOrder

theorem mem_refl_of_alternating_word (s t : Refl G) (i : ℕ): (alternating_word s t (2*i+1)).gprod ∈ Refl G := sorry --please use `refl_induction`

def reflPalindromeProd (s t : Refl G) (i : ℕ) : Refl G := ⟨(alternating_word s t (2*i+1)).gprod, mem_refl_of_alternating_word s t i⟩

def IsReflOrder (R : PartialOrder (Refl G)) := ∀ (s t : Refl G),
    (∀ w : Subgroup.closure {s.1, t.1}, ℓ((s:G)) ≤ ℓ((w : G)) ∧ ℓ((t : G)) ≤ ℓ((w : G))) →
    if orderOf ((s:G)*t) = 0 then
      ∀ (i j : ℕ), i < j → R.lt (reflPalindromeProd s t i) (reflPalindromeProd s t j) ∨
      ∀ (i j : ℕ), i < j → R.lt (reflPalindromeProd t s i) (reflPalindromeProd t s j)
      else
      ∀ (i j : ℕ), i < j → j < orderOf ((s:G)*t) → R.lt (reflPalindromeProd s t i) (reflPalindromeProd s t j) ∨
      ∀ (i j : ℕ), i < j → j < orderOf ((s:G)*t) → R.lt (reflPalindromeProd t s i) (reflPalindromeProd t s j)

end ReflectionOrder
structure ReflectionOrder (G : Type*) [cox : CoxeterGroup G] extends LinearOrder (Refl G) where
  is_refl_order : ReflectionOrder.IsReflOrder toPartialOrder

namespace ReflectionOrder

theorem le_total_of_isReflOrder (R : PartialOrder (Refl G)) (h : IsReflOrder R): ∀ (a b : (Refl G)), R.le a b ∨ R.le b a := sorry --very hard, a paper

noncomputable def ReflectionOrder.mk' {G : Type*} [cox : CoxeterGroup G] (R : PartialOrder (Refl G)) (h : IsReflOrder R) : ReflectionOrder G where
  toPartialOrder := R
  le_total := le_total_of_isReflOrder R h
  decidableLE := by infer_instance
  is_refl_order := h

def Lexico (lino: LinearOrder G) : ReflectionOrder G := by sorry -- not so important

-- instance : Inhabited (ReflectionOrder G) := sorry


#check Interval

end ReflectionOrder


namespace CoxeterGroup

namespace Bruhat

/-- the EL-labeling on a Bruhat interval defined by sending every adjacent pair (a, b) of elements to a * b⁻¹. -/
def ELlabeling (v w : G) : edgeLabeling (Interval v w) (Refl G) := fun
  | .mk ⟨a, b⟩  property => ⟨a * (b⁻¹ : G), sorry⟩

/-
Reference: Dyer_Hecke algberas and shellings of Bruhat intervals

The edge labelling defined above is an EL-labelling of the B
-/
instance ellabeling (v w : G) : ELLabeling (Bruhat.ELlabeling v w) where
  unique := sorry -- very hard
  unique_min := sorry -- hard


end Bruhat

end CoxeterGroup

import Coxeter.CoxeterSystem
import Coxeter.CoxeterMatrix.CoxeterMatrix
import Coxeter.CoxeterMatrix.AlternatingWord
import Coxeter.StrongExchange
import Coxeter.BruhatOrder
import Coxeter.ForMathlib.ELlabeling

import Mathlib.Data.Set.Card

open OrderTwoGen CoxeterMatrix CoxeterGroup PartialOrder AlternatingWord

open Bruhat

variable {G} [cox : CoxeterGroup G]

namespace ReflectionOrder
#check LinearOrder

theorem mem_refl_of_alternating_word (s t : Refl cox.S) (i : ℕ): (alternating_word s t (2*i+1)).gprod ∈ Refl (cox.S) := sorry --please use `refl_induction`

def reflSymmProd (s t : Refl cox.S) (i : ℕ) : Refl cox.S := ⟨(alternating_word s t (2*i+1)).gprod, mem_refl_of_alternating_word s t i⟩

structure _root_.ReflectionOrder (G : Type*) [cox : CoxeterGroup G] extends LinearOrder (Refl cox.S) where
  is_refl_order : ∀ (s t : Refl cox.S) (w : Subgroup.closure {s.1, t.1})
   (i j : ℕ) (hi : i < j) (hj : j < orderOf ((s:G)*t)),
    (ℓ((s:G)) ≤ ℓ((w : G)) ∧  ℓ((t : G)) ≤ ℓ((w : G))) → i < j → j < orderOf ((s:G)*t) → le (reflSymmProd s t i) (reflSymmProd s t j)


def ReflectionOrder.mk' {G : Type*} [cox : CoxeterGroup G] (R : PartialOrder (Refl cox.S)) (h : ∀ (s t : Refl cox.S) (w : Subgroup.closure {s.1, t.1}),
    letI := R;
    ℓ( (s:G) ) ≤ ℓ( (w : G) ) ∧  ℓ( (t : G) ) ≤ ℓ( (w : G) )) : ReflectionOrder G := sorry

def Lexico (lino: LinearOrder cox.S) : ReflectionOrder G := by sorry -- not so important

-- instance : Inhabited (ReflectionOrder G) := sorry


#check Interval

end ReflectionOrder


namespace CoxeterGroup

namespace Bruhat

/-- the EL-labeling on a Bruhat interval defined by sending every adjacent pair (a, b) of elements to a * b⁻¹. -/
def ELlabeling (v w : G) : edgeLabeling (Interval v w) (Refl cox.S) := fun
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

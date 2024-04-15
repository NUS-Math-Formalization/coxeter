import Coxeter.CoxeterSystem
import Coxeter.CoxeterMatrix.CoxeterMatrix
import Coxeter.StrongExchange
import Coxeter.BruhatOrder
import Coxeter.ForMathlib.ELlabeling

import Mathlib.Data.Set.Card

open OrderTwoGen CoxeterMatrix CoxeterGroup PartialOrder

open Bruhat

variable {G} [cox : CoxeterGroup G]

namespace ReflectionOrder

structure _root_.ReflectionOrder (G : Type*) [h : CoxeterGroup G] extends PartialOrder (Refl h.S) where
  is_refl_order : ∀ (s t : Refl h.S) (w : Subgroup.closure {s.1, t.1}),
    ℓ( (s:G) ) ≤ ℓ( (w : G) ) ∧  ℓ( (t : G) ) ≤ ℓ( (w : G) )

def Lexico (lino: LinearOrder cox.S) : ReflectionOrder G := by sorry

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

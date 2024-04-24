import Coxeter.ForMathlib.ASCShelling
import Coxeter.ForMathlib.PosetASC
import Coxeter.ForMathlib.PosetGraded

namespace PartialOrder
open AbstractSimplicialComplex

/-
Definition: Let P be a graded poset. We say P is shellable, if the order complex Delta.ASC is shellable.
-/
def Shellable_Delta (P : Type*) [PartialOrder P] [Fintype P] [GradedPoset P] :=
  Shellable (Delta P)



end PartialOrder

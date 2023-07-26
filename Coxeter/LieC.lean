import Mathlib.Data.Complex.Module
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.BaseChange




section complex_Lie
-- open LieAlgebra

variable (g  : Type _) [LieRing g] [LieAlgebra ℂ g] 

instance i1 : LieRing (RestrictScalars ℝ ℂ g) := rfl

def complexification := TensorProduct  ℝ ℂ (RestrictScalars ℝ ℂ g)



instance complexification.instance.LieAlgebra : LieAlgebra ℂ (complexification g) := by {
  rw [complexification]
  apply LieAlgebra.lieAlgebra  
  
} 


end complex_Lie
import Coxeter.ForMathlib.ELlabeling
import Coxeter.BruhatOrder
import Coxeter.Rpoly

open Classical

local notation "ℛ" => LaurentPolynomial ℤ
local notation "√q" => (LaurentPolynomial.T 1 : ℛ) --`q½`

def genericHeckeAlg (G : Type*) [cox : CoxeterGroup G] := G

import Coxeter.ForMathlib.ELlabeling
import Coxeter.BruhatOrder
import Coxeter.Rpoly
import Coxeter.ReflectionOrder

open Classical


open OrderTwoGen CoxeterMatrix CoxeterGroup PartialOrder

open Bruhat

variable (G : Type*) [cox: CoxeterGroup G]

def InitialSectionReflOrder : Set (Set (Refl cox.S)) :=
  {A : Set (Refl cox.S) | ∃ RO : ReflectionOrder G, @IsLowerSet (Refl cox.S) (RO.toLE) A }












/-
local notation "ℛ" => LaurentPolynomial ℤ
local notation "q½" => (LaurentPolynomial.T 1 : ℛ) -- √q
local notation "q-½" => (LaurentPolynomial.T (-1) : ℛ)

def genericHeckeAlg (G : Type*) [cox : CoxeterGroup G] := G →₀ ℛ

variable {G : Type*} [cox : CoxeterGroup G]

noncomputable instance : AddCommGroup (genericHeckeAlg G) :=
  inferInstanceAs (AddCommGroup (G →₀ ℛ)) -- Finsupp.instAddCommMonoid

noncomputable instance : Module ℛ (genericHeckeAlg G) :=
  inferInstanceAs (Module ℛ (G →₀ ℛ))

noncomputable instance : Module.Free ℛ (genericHeckeAlg G) :=
  inferInstanceAs (Module.Free ℛ (G →₀ ℛ))

noncomputable instance genericHeckeAlg.basis : Basis G ℛ (genericHeckeAlg G) := Finsupp.basisSingleOne

-- instance genericHeckeAlg.mul (a b : genericHeckeAlg G) :
-/

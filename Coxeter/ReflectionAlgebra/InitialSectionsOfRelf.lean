import Coxeter.ForMathlib.ELlabeling
import Coxeter.BruhatOrder
import Coxeter.Rpoly
import Coxeter.ReflectionAlgebra.ReflectionOrder

open Classical


open HOrderTwoGenGroup CoxeterMatrix CoxeterGroup PartialOrder

open Bruhat

noncomputable
section



def InitialSectionReflOrder (G : Type*) [ CoxeterGroup G] : Set (Set (Refl G)) :=
  {A : Set (Refl G) | ∃ R : ReflectionOrder G, @IsLowerSet (Refl G) (R.toLE) A }


-- theorem mul_mem_initialSectionReflOrder {G : Type*} [cox: CoxeterGroup G] (y : G) (A : InitialSectionReflOrder G) : y • (A : Set (Refl G)) ∈  (InitialSectionReflOrder G) := sorry

local notation "ℛ" => LaurentPolynomial ℤ
local notation "q½" => (LaurentPolynomial.T 1 : ℛ) -- √q
local notation "q-½" => (LaurentPolynomial.T (-1) : ℛ)

def ReflAlgebra (G : Type*) [cox: CoxeterGroup G] : Submodule ℛ (G → InitialSectionReflOrder G → ℛ) where
  carrier := {f | Finite ({g : G | ∃ A : InitialSectionReflOrder G, f g A ≠ 0} : Set G) }
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

namespace ReflAlgebra

variable {G : Type*} [cox: CoxeterGroup G]

def dotAction (g : G) (A : InitialSectionReflOrder G) : InitialSectionReflOrder G where
  val := sorry
  property := sorry

protected def mul (f g : ReflAlgebra G) : ReflAlgebra G := sorry

protected def one : ReflAlgebra G := sorry

instance : Ring (ReflAlgebra G) where
  mul := ReflAlgebra.mul
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := ReflAlgebra.one
  one_mul := sorry
  mul_one := sorry
  sub_eq_add_neg := sorry
  zsmul := zsmulRec
  add_left_neg := sorry

instance : Algebra ℛ (ReflAlgebra G) := sorry


end ReflAlgebra









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

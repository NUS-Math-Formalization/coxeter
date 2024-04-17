import Coxeter.ForMathlib.ELlabeling
import Coxeter.BruhatOrder
import Coxeter.Rpoly
import Coxeter.ReflectionAlgebra.ReflectionOrder

open Classical BigOperators


open HOrderTwoGenGroup CoxeterMatrix CoxeterGroup PartialOrder

open Bruhat

noncomputable
section

def IsInitialSectionOf {G : Type*} [CoxeterGroup G] (A : Set (Refl G)) (R  : ReflectionOrder G) : Prop := @IsLowerSet (Refl G) (R.toLE) A

def InitialSectionReflOrder (G : Type*) [CoxeterGroup G] : Set (Set (Refl G)) :=
  {A : Set (Refl G) | ∃ R : ReflectionOrder G, IsInitialSectionOf A R }

-- instance : SetLike

-- theorem mul_mem_initialSectionReflOrder {G : Type*} [cox: CoxeterGroup G] (y : G) (A : InitialSectionReflOrder G) : y • (A : Set (Refl G)) ∈  (InitialSectionReflOrder G) := sorry

local notation "ℛ" => LaurentPolynomial ℤ
local notation "q½" => (LaurentPolynomial.T 1 : ℛ) -- √q
local notation "q-½" => (LaurentPolynomial.T (-1) : ℛ)

def ReflAlgebra (G : Type*) [cox: CoxeterGroup G] : Submodule ℛ (G → InitialSectionReflOrder G → ℛ) where
  carrier := {f | Finite ({g : G | ∃ A : InitialSectionReflOrder G, f g A ≠ 0} : Set G) }
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

instance {G : Type*} [cox: CoxeterGroup G] : FunLike (ReflAlgebra G) G (InitialSectionReflOrder G → ℛ) where
  coe f := f.1
  coe_injective' _ _ := by
    simp

namespace ReflAlgebra

variable {G : Type*} [cox: CoxeterGroup G]

def N (w : G) : Set (Refl G) := {t | ℓ( t * w ) ≤ ℓ(w) }

/-
Nees a coersion for s to be an reflection

lemma Ns_equal_s (s : cox.S) : N s = {s} := by sorry
-/

def conjugate (w : G) (A : Set (Refl G)) : Set (Refl G) := (fun a => (⟨w * a * w⁻¹, sorry⟩ : Refl G) )'' A

def dotAction (w : G) (A : InitialSectionReflOrder G) : InitialSectionReflOrder G where
  val := symmDiff (N w) (conjugate w A)
  property := sorry

lemma dotAction_w_equal_Nw (w : G) : conjugate w ∅ = N w := by sorry

lemma symmDiff_T (A :InitialSectionReflOrder G) : symmDiff (A : Set (Refl G)) ⊤ ∈ InitialSectionReflOrder G := sorry

def mul_index_aux (w : G) (A : InitialSectionReflOrder G) (f g : ReflAlgebra G)  : Set (G × G) :=
  {(x,y) | x * y = w ∧ f.1 x (dotAction y A) ≠ (0: ℛ) ∧ g.1 y A ≠ 0}

instance (w : G) (A : InitialSectionReflOrder G) (f g : ReflAlgebra G) : Fintype (mul_index_aux w A f g) := sorry

protected def mul (f g : ReflAlgebra G) : ReflAlgebra G :=
  ⟨fun w A => ∑ p : mul_index_aux w A f g, (f.1 p.1.1 (dotAction p.1.2 A)) * (g.1 p.1.2 A), sorry⟩

protected def one : ReflAlgebra G := ⟨fun w A => if w = 1 then (1 : ℛ) else 0, sorry⟩

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

def scalarHom : ℛ →+* (ReflAlgebra G) where
  toFun := fun x ↦ ⟨fun w A => if w = 1 then (x : ℛ) else 0, sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

instance : Algebra ℛ (ReflAlgebra G) where
  toFun := scalarHom
  smul r f := (scalarHom r) * f
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry
  smul_def' := sorry


#check ReflAlgebra G
end ReflAlgebra

open ReflAlgebra

namespace HeckeAlgebra

variable {G} [CoxeterGroup G]
#check Subalgebra

def ExistFinset (f : ReflAlgebra G) : Prop := ∀ (w : G), ∃ (T : Finset (Refl G)), ∀ (A B : InitialSectionReflOrder G) (R : ReflectionOrder G),
  IsInitialSectionOf A R → IsInitialSectionOf B R → (A.1 ∩ T) = (B.1 ∩ T) → f.1 w A = f.1 w B

 def xxx (A : InitialSectionReflOrder G)
  (t : Refl G) : Prop := (dotAction (t : G) A).val = symmDiff (A.1) ({t}) ∧ (t ∉ A.1)

def Hecke' (G : Type*) [cox: CoxeterGroup G] :
  Subalgebra ℛ (ReflAlgebra G) where
    carrier := {f | ExistFinset f ∧ ∀ (t : Refl G) (w : G) (A :  InitialSectionReflOrder G ),
      xxx A t → f.1 w A = if w*t < t then f.1 w A else f.1 w A + (q½ - q-½) * (f.1 (w * t) A)}
    mul_mem' := sorry
    add_mem' := sorry
    algebraMap_mem' := sorry

instance : FunLike (Hecke' G) G (InitialSectionReflOrder G → ℛ)  where
  coe f := f.1
  coe_injective' _ _ := by
    simp

open Hecke
#synth Algebra ℛ (Hecke G)
def Hecke'_iso_Hecke: (Hecke' G) ≃ₐ[ℛ] (Hecke G) where
  toFun := fun f => ∑ g : G, ((f.1 g ⟨∅, sorry⟩) • (TT g))
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry
  commutes' := sorry

end HeckeAlgebra




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

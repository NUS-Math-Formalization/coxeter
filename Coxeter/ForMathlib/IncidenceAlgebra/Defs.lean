import Coxeter.ForMathlib.PosetChain
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Intervals.Basic

variable {X R: Type*} [PartialOrder X] [AddGroup R] [LinearOrder Λ] (E: Set (X × X)) (Λ : Type*)

def InitialSection : Set (Set X) := { S | IsLowerSet S }

def HasUpwardFiniteSupport (h : X → R) : Prop := ∀ x : X, (h.support ∩ Set.Ici x).Finite

def edgeOf (x : X)
  : Set E := {⟨(y, z), _⟩| (y < z) ∧ (y = x ∨ z =x) }

-- def Labelling (E: Set (X × X))[LinearOrder Λ] := {f : (E → Λ) // (∀ x : X, f.Injective )}
@[ext]
structure Labelling where
  toFun: E → Λ
  Inj: ∀ x : X, Set.InjOn toFun (edgeOf E x)

instance : FunLike (Labelling E Λ) E Λ where
  coe := Labelling.toFun
  coe_injective' a b _ := by
    ext : 1
    assumption


def unique_extend (h : X → ℛ) :  X → ℛ := sorry

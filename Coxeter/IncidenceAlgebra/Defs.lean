import Coxeter.ForMathlib.PosetChain
import Coxeter.ReflectionAlgebra.InitialSectionsOfRefl
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Intervals.Basic

noncomputable section

open BigOperators

variable {X R: Type*} [PartialOrder X] [AddGroup R] (E: Set (X × X)) (Λ : Type*) [LinearOrder Λ]

local notation "ℛ" => LaurentPolynomial ℤ
local notation "q½" => (LaurentPolynomial.T 1 : ℛ) -- √q
local notation "q-½" => (LaurentPolynomial.T (-1) : ℛ)
local notation "α" => q½ - q-½

def InitialSection : Set (Set Λ) := { S | IsLowerSet S }

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

variable {Λ} in
def InitialSection.Iio (t: Λ) : InitialSection Λ where
  val := Set.Iio t
  property := sorry

variable {Λ} in
def InitialSection.Iic (t: Λ) : InitialSection Λ where
  val := Set.Iic t
  property := sorry

namespace InitialSection


instance : EmptyCollection (InitialSection Λ) where
  emptyCollection := ⟨∅, by tauto⟩

open Classical in
variable {E}{Λ} in
structure HPolynomial (lam: E → Λ) (h: X → InitialSection Λ → ℛ)  : Prop where
  upward_finite: HasUpwardFiniteSupport (fun x => h x ∅)
  support_le : ∀ x : X, ∀ A : InitialSection Λ, (∀ y : X, x ≤ y → h y ∅ = 0) → h x A = 0
  determined_by_finite_set: ∀ (x : X) (A B : InitialSection Λ), ∃ Λ' : Finset Λ,
    (((A : Set Λ) ∩ Λ') = ((B : Set Λ) ∩ Λ')) → (h x A) = (h x B)
  recursive_relation : ∀ (t : Λ), h x (Iic t) =
   if ∃ (e : E), (lam e = t) then h x (Iio t) + α * h x' (Iio t)
    else h x (Iio t)


theorem HPolynomial.unique_extend {lam: E → Λ} {f₁ f₂ :  X → InitialSection Λ → ℛ} (h₁ : HPolynomial lam f₁) (h₂ : HPolynomial lam f₂)
  (h₃: ∀ {x : X}, f₁ x ∅ = f₂ x ∅) : f₁ = f₂ := sorry

structure xxx (L : List X) where
    E_of_adj: ∀ {e : X × X}, e ∈ L.adjPairs → e ∈ E
    adjPair_increasing :
      ((L.adjEPairs.map
        (fun e => (⟨e.1, E_of_adj e.2⟩: E))).map lam).Sorted
    -- ∧ L.head? = some x ∧ L.getLast? = some y

def C_aux (lam : E → Λ ) (x y : X) : Set (List X) :=
   {L : List X |
    (∀ {e : X × X}, e ∈ L.adjPairs → e ∈ E )
    ∧ (L.adjEPairs.map lam).sorted -- Chain' (fun e1 e2  ↦ lam e1 < lam e2)
    ∧ L.head? = some x ∧ L.getLast? = some y}

def C_aux_finite (x y : X) : Finite <| C_aux E x y := sorry

noncomputable def C (x y : X) := Set.Finite.toFinset <| C_aux_finite E x y

--noncomputable def rxy_aux (x y: X)  : C E x y  → ℛ := fun L ↦ (q½ - q-½)^L.1.length

noncomputable def rxy (x y :X) := ∑ x in (C E x y), α^x.length


theorem h_HPolynomial {h }: HPolynomial lam h

def h (x : X) := ∑ y in {y : X | x ≤ y}, (rxy E x y) * (h y ∅)
end InitialSection


end

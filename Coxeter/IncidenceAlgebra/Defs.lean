import Coxeter.ForMathlib.PosetChain
import Coxeter.ReflectionAlgebra.InitialSectionsOfRefl
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Intervals.Basic

noncomputable section

open BigOperators

variable {X R: Type*} [PartialOrder X] [AddGroup R] {E: Set (X × X)} {Λ : Type*} [LinearOrder Λ]

local notation "ℛ" => LaurentPolynomial ℤ
local notation "q½" => (LaurentPolynomial.T 1 : ℛ) -- √q
local notation "q-½" => (LaurentPolynomial.T (-1) : ℛ)
local notation "α" => q½ - q-½

variable (Λ) in
def InitialSection : Set (Set Λ) := { S | IsLowerSet S }

def HasUpwardFiniteSupport (h : X → R) : Prop := ∀ x : X, (h.support ∩ Set.Ici x).Finite

variable (E) in
def edgeOf (x : X)
  : Set E := {⟨(y, z), _⟩| (y < z) ∧ (y = x ∨ z =x) }

-- def Labelling (E: Set (X × X))[LinearOrder Λ] := {f : (E → Λ) // (∀ x : X, f.Injective )}
variable (E) (Λ) in
@[ext]
structure Labelling where
  toFun: E → Λ
  Inj: ∀ x : X, Set.InjOn toFun (edgeOf E x)

instance : FunLike (Labelling E Λ) E Λ where
  coe := Labelling.toFun
  coe_injective' a b _ := by
    ext : 1
    assumption

def InitialSection.Iio (t: Λ) : InitialSection Λ where
  val := Set.Iio t
  property := sorry


def InitialSection.Iic (t: Λ) : InitialSection Λ where
  val := Set.Iic t
  property := sorry

namespace InitialSection


instance : EmptyCollection (InitialSection Λ) where
  emptyCollection := ⟨∅, by tauto⟩

open Classical in
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

structure C_aux (lam: E → Λ) (L : List X) (x y : X) : Prop where
    E_of_adj: ∀ {e : X × X}, e ∈ L.adjPairs → e ∈ E
    adjPair_increasing :
      ((L.adjEPairs.map
        (fun e => (⟨e.val, E_of_adj e.property⟩: E))).map lam).Sorted (· < ·)
    head : L.head? = some x
    tail :  L.getLast? = some y

theorem C_aux_finite (lam: E → Λ) (x y : X) : Finite <| {L | C_aux lam L x y} := sorry

def C (lam: E → Λ) (x y : X) := Set.Finite.toFinset <| C_aux_finite lam x y

--noncomputable def rxy_aux (x y: X)  : C E x y  → ℛ := fun L ↦ (q½ - q-½)^L.1.length

def rxy (lam: E → Λ) (x y :X) := ∑ x in (C lam x y), α^x.length

-- theorem h_HPolynomial : HPolynomial lam h := sorry

-- def h (lam: E → Λ) (x : X) := ∑ y in {y : X | x ≤ y}, (rxy lam x y) * (h y ∅)
end InitialSection


end

import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PresentedGroup
--import Coxeter.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.RingTheory.RootsOfUnity.Basic


import Coxeter.CoxeterSystem


--open Real

section
variable {α : Type*} [DecidableEq α]

variable (m : Matrix α  α ℕ)

class CoxeterMatrix : Prop where
  symmetric : ∀ (a b : α ), m a b = m b a := by aesop
  oneIff: ∀  (a b : α), m a b = 1 ↔ a=b := by aesop
end

open Classical

namespace CoxeterMatrix
variable {α} (m : Matrix α α ℕ) [hm: CoxeterMatrix m]

--variable {m' : Matrix α α ℕ} [hm': CoxeterMatrix m']


lemma one_iff :∀ (a b:α), m a b = 1 ↔ a=b := hm.oneIff

lemma diagonal_one {s : α} : m s s = 1 := by rw [hm.oneIff]

lemma off_diagonal_ne_one {s : α} : s ≠ t → m s t ≠ 1 := by simp [hm.oneIff]


local notation  "F" => FreeGroup α

@[simp] def toRelation (s t : α) (n : ℕ ) : F := (FreeGroup.of s * FreeGroup.of t)^n

@[simp] def toRelation'  (s : α × α ) : F :=toRelation s.1 s.2 (m s.1 s.2)

def toRelationSet : (Set F) := Set.range <| toRelation' m

def toGroup := PresentedGroup <| toRelationSet m

local notation "N" => Subgroup.normalClosure (toRelationSet m)
local notation "G" => toGroup m

instance : Group <| toGroup m := QuotientGroup.Quotient.group _

def of (x : α) : G := QuotientGroup.mk' N (FreeGroup.of x)


-- The set of simple reflections
@[simp]
abbrev SimpleRefl := Set.range (of m)


local notation "S" => (SimpleRefl m)

@[simp]
abbrev  Refl : Set G := Set.range <| fun ((g,s): G×S) => g * s * g⁻¹

local notation "T" => (Refl m)

@[simp]
lemma SimpleRefl_subset_Refl : ∀ {g : G}, g ∈ S → g ∈ T := by
  rintro g ⟨s, hs⟩
  use ⟨1, ⟨g, by rw [Set.mem_range]; use s⟩⟩
  simp

@[simp]
def toSimpleRefl (a : α) : SimpleRefl m := ⟨of m a, by  simp⟩

instance coe_group: Coe α (toGroup m) where
  coe := of m

instance coe_simple_refl: Coe α (SimpleRefl m) where
  coe := toSimpleRefl m

def liftHom_aux {A:Type*} [Group A] (f : α → A)  (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) : ∀ r ∈ toRelationSet m, (FreeGroup.lift f) r = 1 := by
  intro r hr
  obtain ⟨⟨s,t⟩,hst⟩ := hr
  simp only [toRelation', toRelation] at hst
  simp only [<- hst, map_pow, map_mul, FreeGroup.lift.of, h]

-- Lift map from α→ A to Coxeter group → A
def lift {A : Type _} [Group A] (f : α → A)  (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) : G →* A := PresentedGroup.toGroup <| liftHom_aux m f h


lemma lift.of {A : Type _} [Group A] (f : α → A) (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) (s : α) : lift m f h (of m s) = f s := by
  apply PresentedGroup.toGroup.of


abbrev μ₂ := rootsOfUnity 2 ℤ
@[simp]
abbrev μ₂.gen :μ₂ := ⟨-1,by norm_cast⟩

lemma μ₂.gen_ne_one : μ₂.gen ≠ 1 := by rw [μ₂.gen]; norm_cast

@[simp]
def epsilon : G →* μ₂  := lift m (fun _=> μ₂.gen) (by intro s t; ext;simp)

lemma epsilon_of (s : α) : epsilon m (of m s) = μ₂.gen := by
  simp only [epsilon, lift.of m]



--@[simp] lemma of_mul (x y: α) : (of m x) * (of m y) =
--QuotientGroup.mk' _  (FreeGroup.mk [(x,tt), (y,tt)]):= by rw [of];

@[simp]
lemma of_relation (s t: α) : ((of m s) * (of m t))^(m s t) = 1  :=  by sorry

@[simp]
lemma of_square_eq_one {s : α} : (of m s) * (of m s) = 1  :=  by sorry

@[simp]
lemma of_square_eq_one' : s ∈ SimpleRefl m → s * s = 1 := by
  simp only [SimpleRefl, Set.mem_range, forall_exists_index]
  intro x h
  simp_all only [← h, of_square_eq_one]

lemma of_inv_eq_of {x : α} :  (of m x)⁻¹ =  of m x  :=
  inv_eq_of_mul_eq_one_left (@of_square_eq_one α m x)

lemma toGroup_expression : ∀ x :G, ∃ L : List S,  x = L.gprod := by sorry


lemma generator_ne_one  (s: α) : of m s ≠ 1 :=  by
  intro h
  have h1 :epsilon m (of m s) = 1 := by rw [h];simp
  have h2 :epsilon m (of m s) = μ₂.gen := by rw [epsilon_of]
  rw [h2] at h1; exact μ₂.gen_ne_one h1


lemma generator_ne_one'  {x: G} : x ∈ S → x ≠ 1 :=  by
  rintro ⟨s, hs⟩
  rw [← hs]
  exact generator_ne_one m s

lemma order_two :  ∀ (x: G) , x ∈ S →  x * x = (1 : G) ∧ x ≠ 1 :=  by
  rintro x ⟨s, hs⟩
  rw [← hs]
  exact ⟨of_square_eq_one m, generator_ne_one m s⟩


instance ofOrderTwoGen : OrderTwoGen (SimpleRefl m)  where
  order_two := order_two m
  expression := toGroup_expression m

end CoxeterMatrix


namespace CoxeterMatrix
open OrderTwoGen

variable {α} {m : Matrix α α ℕ} [hm: CoxeterMatrix m]

local notation "G" => toGroup m
local notation "S" => SimpleRefl m
local notation "T" => Refl m


local notation : max "ℓ(" g ")" => (OrderTwoGen.length S g)

lemma epsilon_length  {g : G} : epsilon m g = (μ₂.gen)^(ℓ(g)) := by
  sorry


lemma length_smul_neq {g : G} {s:S} : ℓ(g) ≠ ℓ(s*g) := by
  sorry

lemma length_muls_neq {g : G} {s:S} : ℓ(g) ≠ ℓ(g*s) := by
  sorry

lemma length_diff_one  {g : G} {s:S} : ℓ(s*g) = ℓ(g) + 1  ∨ ℓ(g) = ℓ(s*g) + 1 := by
  by_cases h : ℓ(s*g) > ℓ(g)
  . left
    have : ℓ(s*g) ≤ ℓ(g) + 1:= length_smul_le_length_add_one
    linarith
  . right
    have : ℓ(g) ≤ ℓ(s*g) + 1 := sorry--length_smul_le_length_add_one
    have : ℓ(g) ≠ ℓ(s*g) := by sorry
    sorry

lemma length_smul_lt_of_le {g : G} {s : S} (hlen : ℓ(s * g) ≤ ℓ(g)) : ℓ(s * g) < ℓ(g):= by
  sorry



def strong_exchange : ∀ (L : List S) ( t : T) , ℓ((t:G) * L) < ℓ(L) → ∃ (i:Fin L.length), (t:G) * L = (L.removeNth i) := by
  sorry



def exchange: OrderTwoGen.ExchangeProp S:= by
  intro L t _ h2
  obtain ⟨i, hi⟩ := strong_exchange L ⟨t.val, (SimpleRefl_subset_Refl m t.prop)⟩ (length_smul_lt_of_le h2)
  exact ⟨i, hi⟩



end CoxeterMatrix



namespace CoxeterMatrix
open OrderTwoGen

variable {α : Type*} [DecidableEq α] {m : Matrix α α ℕ} [CoxeterMatrix m]



-- We will covert the lean3 proof to lean4
lemma deletion_prop : DeletionProp (SimpleRefl m) := by sorry


instance ofCoxeterSystem : CoxeterSystem (SimpleRefl m) where
  order_two := order_two m
  expression := toGroup_expression m
  exchange := deletion_imp_exchange (SimpleRefl m) deletion_prop


instance ofCoxeterGroup : CoxeterGroup  (toGroup m)  where
  S := SimpleRefl m
  order_two := order_two m
  expression := toGroup_expression m
  exchange := deletion_imp_exchange (SimpleRefl m) deletion_prop

end CoxeterMatrix

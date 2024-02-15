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

/-- A matrix `IsCoxeter` if it is a symmetric matrix with diagonal entries equal to one
and off-diagonal entries distinct from one. -/
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
def toSimpleRefl (a : α) : SimpleRefl m := ⟨of m a, by  simp⟩

instance coe_group: Coe α (toGroup m) where
  coe := of m

instance coe_simple_refl: Coe α (SimpleRefl m) where
  coe := toSimpleRefl m


-- Lift homomorphism from map to Coxeter map
def liftHom {A : Type _} [Group A] (f : α → A)  (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) : G →* A := QuotientGroup.lift N (FreeGroup.lift f) (by sorry)

lemma liftHom.of {A : Type _} [Group A] (f : α → A) (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) (s : α) : liftHom m f h (of m s) = f s := by
  rw [liftHom,CoxeterMatrix.of]
  sorry

abbrev μ₂ := rootsOfUnity 2 ℤ
@[simp]
abbrev μ₂.gen :μ₂ := ⟨-1,by norm_cast⟩

lemma μ₂.gen_ne_one : μ₂.gen ≠ 1 := by rw [μ₂.gen]; norm_cast

@[simp]
def epsilon : G →* μ₂  := liftHom m (fun _=> μ₂.gen) (by intro s t; ext;simp)

lemma epsilon_of (s : α) : epsilon m (of m s) = μ₂.gen := by
  simp only [epsilon, liftHom.of m]



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




noncomputable section GeometricRepresentation
--variable {α : Type*} [DecidableEq α]
--variable (m : Matrix α  α ℕ) [CoxeterMatrix m]



class Splitting (k : Matrix α α ℝ) where
  m_eq_one : ∀ s s': α, m s s' = 1 → k s s' = -2
  m_eq_two : ∀ s s' : α , m s s' = 2 → k s s' = 0
  m_gt_three : ∀ s s' : α, 3 ≤ m s s' → k s s' * k s' s = 4 * (Real.cos (Real.pi / m s s'))^2 ∧ (0 < k s s')
  m_eq_zero : ∀ s s' :α, m s s' = 0 → 4 ≤ k s s' * k s' s ∧ (0 < k s s')

#check Splitting
@[simp]
abbrev kk_aux : ℕ → ℝ
| 0 => 3
| 1 => -2
| 2 => 0
| (n + 3) => 2 * Real.cos ( Real.pi / (n+3))


def kk [CoxeterMatrix m] : Matrix α α ℝ := fun s s': α => kk_aux <| m s s'

instance kk.split : Splitting m (kk m) := by sorry

--variable {m : Matrix α  α ℕ} [CoxeterMatrix m]

local notation:130 "V⋆" => α → ℝ

local notation "k" => kk m
--local notation:120 a:121 "⋆" => Pi.single a 1

noncomputable def sigma_star  (s:α) : (V⋆) →ₗ[ℝ] (V⋆) where
  toFun := fun p s' =>  p s' + (p s) *  (k s s')
  map_add' := by sorry
  map_smul' := by sorry

local notation "σ⋆" => sigma_star m

@[simp]
lemma sigma_star_one  {s s': α} {p : V⋆} : m s s' = 1 →  (σ⋆ s p) s' = - (p s) := by sorry

@[simp]
lemma sigma_star_two  : ∀ (s s': α) (p : V⋆), m s s' = 2 → (σ⋆ s p) s' = p s' := by sorry


@[simp]
lemma sigma_star_gt_tree  : ∀ (s s': α) (p : V⋆), 3 ≤ m s s' ∨ m s s' = 0 → (σ⋆ s p) s' = p s'+ p s * (k s s') := by sorry

lemma sigma_star_order_two : (σ⋆ s)^2 = 1:= by sorry

lemma sigma_star_mul_apply_s'_eq_two  {p : V⋆} (h: m s s' = 2) : ((σ⋆ s) * (σ⋆ s')) p s' = - p s' := by sorry


-- add some other lemmas
-- The final goal is
lemma order_sigma_star_mul : orderOf ((σ⋆ s) * (σ⋆ s')) = m s s' := by sorry

lemma order_generator_mul (s t :α) : orderOf (CoxeterMatrix.of m s * CoxeterMatrix.of m t) = m s t := by sorry



end GeometricRepresentation


end CoxeterMatrix

namespace CoxeterMatrix

#check order_generator_mul

-- This is non-trivial, one have to compute the order of the product of two generators.
lemma of_injective (a b :α) : of m a = of m b ↔ a = b:= by
  constructor
  . sorry
  . intro ;congr

end CoxeterMatrix

namespace CoxeterMatrix
open OrderTwoGen

variable {α : Type*} [DecidableEq α] {m : Matrix α α ℕ} [CoxeterMatrix m]

instance ofOrderTwoGen : OrderTwoGen (SimpleRefl m)  where
  order_two := order_two m
  expression := toGroup_expression m


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

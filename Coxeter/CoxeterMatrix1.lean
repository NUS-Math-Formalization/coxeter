import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PresentedGroup
--import Coxeter.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Exponential

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

variable (m' : Matrix α α ℕ) [hm': CoxeterMatrix m']


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
def liftHom {A : Type _} [Group A] {f : α → A}  (h : ∀ (s t: α ), (f s * f t)^(m s t) = 1) : G →* A := QuotientGroup.lift N (FreeGroup.lift f) (by sorry)

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

lemma toGroup_surj : ∀ x :G, ∃ L : List S,  L.gprod  = x := by sorry


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


def kk : Matrix α α ℝ := fun s s': α => kk_aux <| m s s'

instance kk.split : Splitting m (kk m) := by sorry

local notation:130 "V⋆" => α →₀ ℝ

local notation:110 "k" => kk m
local notation:120 a:121 "⋆" => Finsupp.single a 1

variable (a :α)
#check a⋆


noncomputable def sigma_star  (s : α) := fun p:V⋆ => p + (p s) • (fun (s': α) => k s s'))

-- α_star


end GeometricRepresentation

end CoxeterMatrix

namespace CoxeterMatrix


-- This is non-trivial, one have to compute the order of the product of two generators.
lemma of_injective (a b :α) : of m a = of m b ↔ a = b:= by
  constructor
  . sorry
  . intro ;congr

end CoxeterMatrix



lemma Coxeter_matrix_of_group.isSymm [CoxeterSystem G S] (s₁ s₂ : S) : orderOf (s₁ * s₂:G) = orderOf (s₂ * s₁:G) := by
  rw [←orderOf_inv (s₁*s₂:G),mul_inv_rev,←inv_eq_self _ s₁.2,←inv_eq_self _ s₂.2]

lemma Coxeter_matrix_of_group.oneIff [CoxeterSystem G S] (s₁ s₂ : S) : orderOf (s₁ * s₂:G) = 1 ↔ s₁ = s₂ := sorry

noncomputable def CoxeterMatrixOfCoxeterGroup (S : Set G) [orderTwoGen S] [CoxeterSystem G S]: @CoxeterMatrix S where
  m      := fun s₁ s₂ => orderOf (s₁ * s₂:G)
  isSymm := by intros a b; dsimp; exact @Coxeter_matrix_of_group.isSymm G _ S _ _ a b
  oneIff := by apply Coxeter_matrix_of_group.oneIff

instance (m : @CoxeterMatrix α): @orderTwoGen m.toGroup _ (m.SS) :=sorry

instance CoxeterGroupOfCoxeterMatrix (m : @CoxeterMatrix α) : CoxeterSystem m.toGroup m.SS where
  exchange :=sorry
  deletion :=sorry

-- noncomputable def freeGroupOfStoCoxeter (x : FreeGroup S) : G := List.gprod <| (List.unzip <| FreeGroup.toWord x).1

-- instance : Setoid (FreeGroup S)  where
--   r := fun x y => (freeGroupOfStoCoxeter x = freeGroupOfStoCoxeter y)
--   iseqv :=sorry




-- def CoxeterGroupLiftisHom {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S] {A : Type _} [Group A] (f : S → A) ( h : ∀ (s : S × S), (f s.1 * f s.2)^( (CoxeterMatrixOfCoxeterGroup S).m s.1 s.2) = 1 ) : G →* A where
--   toFun := Quotient.lift  (FreeGroup.lift f) _
--   map_one' :=sorry
--   map_mul' :=sorry

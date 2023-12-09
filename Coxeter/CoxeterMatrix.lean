import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.OrderOfElement
import Coxeter.Basic


universe u1 u2 u3

variable {α: Type u1} {β: Type u2}  {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S]
local notation:max "ℓ(" g ")" => (@length G _ S _ g)


@[ext,class] structure CoxeterMatrix {α : Type u1}:=
(m : Matrix α α ℕ)
(isSymm : ∀ (a b : α ), m a b = m b a )
(one_iff: ∀  {a b : α}, (m a b = 1) ↔ (a=b) )

namespace CoxeterMatrix

variable (m : @CoxeterMatrix α)

lemma Diag_is_one {s : α} : m.m s s = 1 := by
   rw [m.one_iff]

local notation  "F" => FreeGroup α

@[simp] def RelTwoElements (s t : α) (n : ℕ ) : F := (FreeGroup.mk [(s,true),(t,true)])^n


@[simp] def toRelation'  (s : α × α ) : F :=
RelTwoElements s.1 s.2 (m.m s.1 s.2)
-- (FreeGroup.mk [(s.1,true), (s.2, true)])^(m.m s.1 s.2)


def toRelationSet : (Set F):=
Set.image (toRelation' m) Set.univ
#check toRelationSet


def toGroup := PresentedGroup (m.toRelationSet)

local notation "N" => Subgroup.normalClosure m.toRelationSet
local notation "G" => m.toGroup

instance : Group m.toGroup := QuotientGroup.Quotient.group _

/-
-- Coxeter group is a quotient group
example :  m.toGroup = (F ⧸ N)  := by rfl
-/

def of (x : α) : G :=
QuotientGroup.mk' N (FreeGroup.of x)

-- The set of simple reflections
def SS := Set.image (m.of) Set.univ

@[simp]
def alpha_to_SS (a : α) : ↑ m.SS := ⟨m.of a, by {
  apply Set.mem_image_of_mem
  simp
}⟩

instance : @orderTwoGen m.toGroup _ (SS m) :=sorry

#check length

instance : @CoxeterSystem m.toGroup (SS m) _ _ where
exchange:=sorry
deletion:=sorry


end CoxeterMatrix


noncomputable def Coxeter_matrix_of_group_aux (s₁ s₂ : S):= orderOf (s₁*s₂:G)

lemma Coxeter_matrix_of_group_isSymm (s₁ s₂ : S):  orderOf (s₁*s₂:G) = orderOf (s₂*s₁:G) := sorry

noncomputable def Coxeter_matrix_of_group : @CoxeterMatrix S where
m:= Coxeter_matrix_of_group_aux
isSymm:= by {
  intros s₁ s₂
  apply Coxeter_matrix_of_group_isSymm
  }
one_iff:= by {
  intros s₁ s₂
  simp [Coxeter_matrix_of_group_aux]
  constructor
  . intros H
    have h2 :=inv_eq_of_mul_eq_one_right H
    have h1 :=@inv_eq_self G _  S _ s₁ (Subtype.mem s₁)
    apply Subtype.ext
    rw [h1]
    assumption
  . intros H
    rw [H]
    exact (@orderTwoGen.order_two G _  S _ s₂ (Subtype.mem s₂)).1}

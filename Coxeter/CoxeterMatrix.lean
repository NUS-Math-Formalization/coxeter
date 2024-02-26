import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.OrderOfElement
import Coxeter.Basic


universe u1 u2 u3

open Classical

variable {α: Type u1} {β: Type u2}  {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S]

@[ext,class] structure CoxeterMatrix {α : Type u1}:=
  (m : Matrix α α ℕ)
  (isSymm : ∀ (a b : α ), m a b = m b a )
  (oneIff: ∀  {a b : α}, (m a b = 1) ↔ (a=b) )

namespace CoxeterMatrix

variable (m : @CoxeterMatrix α)

lemma Diag_is_one {s : α} : m.m s s = 1 := by rw [m.oneIff]

local notation  "F" => FreeGroup α

@[simp] def RelTwoElements (s t : α) (n : ℕ ) : F := (FreeGroup.mk [(s,true),(t,true)])^n

@[simp] def toRelation'  (s : α × α ) : F :=RelTwoElements s.1 s.2 (m.m s.1 s.2)

def toRelationSet : (Set F) := Set.image (toRelation' m) Set.univ

def toGroup := PresentedGroup (m.toRelationSet)

local notation "N" => Subgroup.normalClosure m.toRelationSet
local notation "G" => m.toGroup

instance : Group m.toGroup := QuotientGroup.Quotient.group _

def of (x : α) : G := QuotientGroup.mk' N (FreeGroup.of x)

-- The set of simple reflections
def SS := Set.image (m.of) Set.univ

@[simp]
def alpha_to_SS (a : α) : ↑ m.SS := ⟨m.of a, by {
  apply Set.mem_image_of_mem
  simp
}⟩


end CoxeterMatrix

variable {m:@CoxeterMatrix α}

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

@[simp] def RelTwoElements' (s t : S) (n : ℕ ) : FreeGroup S := (FreeGroup.mk [(s,true),(t,true)])^n

@[simp] noncomputable def toRelation''  (s : S × S) : FreeGroup S :=RelTwoElements' s.1 s.2 ((CoxeterMatrixOfCoxeterGroup S).m s.1 s.2)

def toRelationSet  (S : Set G) [orderTwoGen S] [CoxeterSystem G S] := Set.image (@toRelation'' G _ S _ _) Set.univ

local notation  "N'(" S ")" => Subgroup.normalClosure (toRelationSet S)

instance CoxeterEquiv {G : Type _} [Group G] (S :Set G) [orderTwoGen S] [CoxeterSystem G S] : G ≃* ((FreeGroup S) ⧸ N'(S)) where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
-- instance : HasEquiv (FreeGroup S) := instHasEquiv

def FreeGroupLift {A : Type _} [Group A] (f : S → A) : (FreeGroup S) → A :=FreeGroup.lift f

lemma liftAux  {A : Type _} [Group A] (f : S → A) ( h : ∀ (s : S × S), (f s.1 * f s.2)^( (CoxeterMatrixOfCoxeterGroup S).m s.1 s.2) = 1 ): N'(S) ≤ MonoidHom.ker (FreeGroup.lift f):=by sorry

def CoxeterGroupLift {A : Type _} [Group A] (f : S → A) ( h : ∀ (s : S × S), (f s.1 * f s.2)^( (CoxeterMatrixOfCoxeterGroup S).m s.1 s.2) = 1 ) : G →* A := MonoidHom.comp (QuotientGroup.lift N'(S) (FreeGroup.lift f) (liftAux f h)) (CoxeterEquiv S)



-- def CoxeterGroupLiftisHom {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S] {A : Type _} [Group A] (f : S → A) ( h : ∀ (s : S × S), (f s.1 * f s.2)^( (CoxeterMatrixOfCoxeterGroup S).m s.1 s.2) = 1 ) : G →* A where
--   toFun := Quotient.lift  (FreeGroup.lift f) _
--   map_one' :=sorry
--   map_mul' :=sorry

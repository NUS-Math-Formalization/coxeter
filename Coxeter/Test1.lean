import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Real.Basic


/-
universe u1 u2 u3

variable {α : Type u1}




class Basis (S : Set (FreeGroup α)) where
  ι : FreeGroup S ≃* FreeGroup α
 -/



 class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'



def lt_wfRel : WellFoundedRelation Nat where
  rel := Nat.lt
  wf  := by
    apply WellFounded.intro
    intro n
    induction n with
    | zero      =>
      apply Acc.intro 0
      intro _ h
      apply absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      apply Acc.intro (Nat.succ n)
      intro m h
      have : m = n ∨ m < n := Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h)
      match this with
      | Or.inl e => subst e; assumption
      | Or.inr e => exact Acc.inv ih e

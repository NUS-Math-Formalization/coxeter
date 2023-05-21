import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Basic


variable {G : Type _} [Group G] (a b c : G)


/- 
Hungerford Chapter II Exercises 8.2 
-/
example : ⁅a, b⁆ =  a * b * a⁻¹ * b⁻¹ := rfl  
example : ⁅a * b, c⁆  = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆  := by sorry  -- try ``group'' 



/-
Inequalities involving natural numbers
-/
example (n : ℕ): n ≤ 1 ↔ n =0 ∨ n=1 := 
by {
  match n with 
  | 0 => simp
  | 1 => simp
  | n+2 => simp
} 


example (n : ℕ): n ≤ 1 ↔ n =0 ∨ n=1 := 
by {
   rw [<-Nat.lt_one_iff]
   exact Iff.intro lt_or_eq_of_le le_of_lt_or_eq 
} 
































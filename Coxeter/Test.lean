import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Basic



def length' {α : Type _} : List α → ℕ  
 | List.nil     => 0
 | List.cons head tail => 1 + length' tail 

#eval length' [1,2,1]


#check mul_inv_rev
#check mul_left_cancel_iff

variable {G : Type _} [Group G] (a b c : G)

/- Hungerford, Algebra Chapter II Exercises 8.2 -/
example : ⁅a, b⁆ =  a * b * a⁻¹ * b⁻¹ := rfl  
example : ⁅a * b, c⁆  = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆  := by group 

/-
{
  sorry
  --rw [Bracket.bracket,commutatorElement]
  --simp
  --repeat rw [<-mul_assoc] 
  --repeat rw [mul_right_cancel_iff] 
  --repeat rw [mul_assoc] 
  --repeat rw [mul_left_cancel_iff] 
  --simp
}
-/

-- try ``group'' 



/- Inequalities involving natural numbers -/
example (n : ℕ): n ≤ 1 ↔ n =0 ∨ n=1 := 
by {
  match n with 
  | 0 => simp
  | 1 => simp
  | n+2 => simp?
} 


example (n : ℕ): n ≤ 1 ↔ n =0 ∨ n=1 := 
by {
   rw [<-Nat.lt_one_iff]
   exact Iff.intro lt_or_eq_of_le le_of_lt_or_eq 
} 

example : ∃ (n : ℕ),   n-1 = n := by  use 0  































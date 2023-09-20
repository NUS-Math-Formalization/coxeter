import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Init.Order.Defs

variable (R : Type*) [Ring R]

#check Nat

def f (x : ℕ) :=
  x + 3

#check f

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

theorem my_add_neg_cancel_right (a b : R) : a + b + -b = a := by
  {rw [add_assoc,add_right_neg,add_zero]}

example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say m and n are natural numbers, and assume n=2*k.
  rintro m n ⟨k, hk⟩
  -- We need to prove m*n is twice a natural number. Let's show it's twice m*k.
  use m * k
  -- Substitute for n,
  rw [hk]
  -- and now it's obvious.
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
 rw [mul_comm ,←mul_assoc,mul_comm]

  
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  linarith

variable (a b c :ℝ)

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

variable (R : Type*) [Ring R]


theorem self_sub (a : R) : a - a = 0 := by
  sorry


example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁
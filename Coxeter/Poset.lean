import Coxeter.CoxeterSystem

import Mathlib.Data.Set.Card


variable {P : Type*} [PartialOrder P]

def ledot (a b : P) := a < b ∧ (∀ c : P, a ≤ c ≤ b, (a = c ∨ b = c))

import Mathlib.GroupTheory.PresentedGroup
import ./CoxeterMatrix



class CoxeterGroup :=  extend 
(S : Set α α ℕ)
(isSymm : ∀ (a b : α ), m a b = m b a )
(one_iff: ∀  {a b : α}, (m a b = 1) ↔ (a=b) )
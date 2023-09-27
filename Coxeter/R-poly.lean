import Coxeter.Basic
import Coxeter.newBruhat



import Mathlib.Data.Polynomial.Basic

variable {G : Type _} [Group G] {S :Set G} [orderTwoGen S] [CoxeterSystem G S] [LT G] [LE G] 


-- class Rploy (u v:G)  (R_ploy : Polynomial ℤ) where
--   not_le: ¬ (u ≤ v) → R_ploy = 0
--   eq: u = v → R_ploy = 1
--   sMemD_Ru: ∀ s ∈ D_R v, s∈D_R u → R_ploy = R

inductive 

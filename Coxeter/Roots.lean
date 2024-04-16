import Coxeter.Basic
import Coxeter.CoxeterMatrix.CoxeterMatrix

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Classical
universe u1


class split (k : α → α → ℝ)(m : @CoxeterMatrix α) :=
(m_eq_one : ∀ s s': α, m.m s s' = 1 → k s s' = -2)
(m_eq_two : ∀ s s' : α , m.m s s' = 2 → k s s' = 0)
(m_gt_three : ∀ s s' : α, 3 ≤ m.m s s' → k s s' * k s' s = 4 * (Real.cos (Real.pi / m.m s s'))^2 ∧ (0 < k s s'))
(m_eq_zero : ∀ s s' :α, m.m s s' = 0 → 4 ≤ k s s' * k s' s ∧ (0 < k s s'))

#check split

@[simp]
noncomputable def kk_aux : ℕ → ℝ
| 0 => 3
| 1 => -2
| 2 => 0
| (n + 3) => 2 * Real.cos (Real.pi / (n+3))

noncomputable def kk (m : @CoxeterMatrix α) : α → α → ℝ := fun s s': α => kk_aux (m.m s s')

instance kk.split : split (kk m) m := by{
  -- m_eq_one := by {
  -- intros s s' hs
  -- simp_rw [kk,hs,kk_aux]
  -- }
  -- m_eq_two := by {
  --   intros s s' hs
  --   simp_rw [kk,hs,kk_aux]}
  -- m_gt_three := by {
  --   intros s s' hs
  --   simp_rw [kk]
  --   have hss:=Nat.add_sub_of_le hs
  --   rw [add_comm] at hss
  --   rw[ ←hss,kk_aux]
  --   nth_rewrite 1 [m.isSymm] at hss
  --   rw [←hss,kk_aux]
  --   split
  --   {--rw [pow_two,mul_assoc]
  --   sorry
  --   }
  --   sorry
  --   }

  -- m_eq_zero := by {
  --   intros s s' hs
  --   simp_rw [kk]
  --   rw [hs,kk_aux]
  --   rw [m.isSymm] at hs
  --   rw [hs,kk_aux]
  --   sorry}
sorry
}


variable {G : Type _} [Group G] {S :Set G} [orderTwoGen S] {m : @CoxeterMatrix S}

def V_S := S → ℝ

def V_S_star := (S → ℝ) → ℝ

#check V_S

instance V_S.add : AddCommMonoid (@V_S G S) := @Pi.addCommMonoid S _ _

noncomputable instance V_S.smul : SMul ℝ (@V_S G S):= Pi.instSMul

noncomputable instance V_S.module : Module ℝ (@V_S G S):= Pi.Function.module S ℝ ℝ

noncomputable instance V_S_End.monoid : Monoid (Module.End ℝ (@V_S G S)) := Module.End.monoid

noncomputable def sigma  (s : S) (p: S → ℝ) : S → ℝ := p + ((p s) • (fun s' => kk m s s'))

noncomputable def α_s (s : S) : S → ℝ := fun s' => ite (s = s') 1 0

variable {s:S} {L:List S}
#check sigma s

#check (List.map (fun (s:S) => @sigma G S m s) L)

noncomputable def sigma' (L:List S) := List.map (fun (s:S) => @sigma G S m s) L

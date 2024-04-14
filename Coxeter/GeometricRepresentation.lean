import Coxeter.CoxeterMatrix.CoxeterMatrix


variable {α : Type*} [DecidableEq α]

variable (m : Matrix α  α ℕ) [CoxeterMatrix m]

namespace GeometricRepresentation
--variable {α : Type*} [DecidableEq α]
--variable (m : Matrix α  α ℕ) [CoxeterMatrix m]
noncomputable section


class Splitting (k : Matrix α α ℝ) where
  m_eq_one : ∀ s s': α, m s s' = 1 → k s s' = -2
  m_eq_two : ∀ s s' : α , m s s' = 2 → k s s' = 0
  m_gt_three : ∀ s s' : α, 3 ≤ m s s' → k s s' * k s' s = 4 * (Real.cos (Real.pi / m s s'))^2 ∧ (0 < k s s')
  m_eq_zero : ∀ s s' :α, m s s' = 0 → 4 ≤ k s s' * k s' s ∧ (0 < k s s')

#check Splitting
@[simp]
abbrev kk_aux : ℕ → ℝ
| 0 => 3
| 1 => -2
| 2 => 0
| (n + 3) => 2 * Real.cos ( Real.pi / (n+3))


def kk [CoxeterMatrix m] : Matrix α α ℝ := fun s s': α => kk_aux <| m s s'

instance kk.split : Splitting m (kk m) := by sorry

--variable {m : Matrix α  α ℕ} [CoxeterMatrix m]

local notation:130 "V⋆" => α → ℝ

local notation "k" => kk m
--local notation:120 a:121 "⋆" => Pi.single a 1

noncomputable def sigma_star  (s:α) : (V⋆) →ₗ[ℝ] (V⋆) where
  toFun := fun p s' =>  p s' + (p s) *  (k s s')
  map_add' := by sorry
  map_smul' := by sorry

local notation "σ⋆" => sigma_star m

@[simp]
lemma sigma_star_one  {s s': α} {p : V⋆} : m s s' = 1 →  (σ⋆ s p) s' = - (p s) := by sorry

@[simp]
lemma sigma_star_two  : ∀ (s s': α) (p : V⋆), m s s' = 2 → (σ⋆ s p) s' = p s' := by sorry


@[simp]
lemma sigma_star_gt_tree  : ∀ (s s': α) (p : V⋆), 3 ≤ m s s' ∨ m s s' = 0 → (σ⋆ s p) s' = p s'+ p s * (k s s') := by sorry

lemma sigma_star_order_two : (σ⋆ s)^2 = 1:= by sorry

lemma sigma_star_mul_apply_s'_eq_two  {p : V⋆} (h: m s s' = 2) : ((σ⋆ s) * (σ⋆ s')) p s' = - p s' := by sorry


-- add some other lemmas
-- The final goal is
lemma order_sigma_star_mul : orderOf ((σ⋆ s) * (σ⋆ s')) = m s s' := by sorry

end
end GeometricRepresentation

namespace CoxeterMatrix

lemma order_generator_mul (s t :α) : orderOf (CoxeterMatrix.of m s * CoxeterMatrix.of m t) = m s t := by sorry

lemma of_injective (a b :α) : of m a = of m b ↔ a = b:= by
  constructor
  . contrapose; intro h; by_contra h2
    have : (of m a) * (of m b) = 1 := by simp [h2]
    rw [<-orderOf_eq_one_iff,order_generator_mul,one_iff] at this
    exact h this
  . intro ;congr

end CoxeterMatrix

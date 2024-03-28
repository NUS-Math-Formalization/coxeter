import Mathlib.Tactic.Rify

import Coxeter.CoxeterMatrix

open BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

variable (m : Matrix α α ℕ) [mh: CoxeterMatrix m]

namespace GeometricRepresentation
--variable {α : Type*} [DecidableEq α]
--variable (m : Matrix α  α ℕ) [CoxeterMatrix m]

-- working in real numbers, need noncomputable
noncomputable section

/-- A map k : α × α → ℝ is called a splitting if for every s, s' in α:
- k(s, s') = -2 if m(s, s') = 1;
- k(s, s') = 0 if m(s, s') = 2;
- k(s, s') ≥ 0 if m(s, s') = 0 or m(s, s') ≥ 3;
- k(s, s') * k(s', s) ≥ 4 cos²(π / m(s, s')) if m(s, s') ≥ 3;
- k(s, s') * k(s', s) ≥ 4 if m(s, s') = 0. -/
class Splitting (k : Matrix α α ℝ) where
  m_eq_one : ∀ s s': α, m s s' = 1
    → k s s' = -2
  m_eq_two : ∀ s s' : α , m s s' = 2
    → k s s' = 0
  m_eq_zero : ∀ s s' :α, m s s' = 0
    → 4 ≤ k s s' * k s' s ∧ (0 < k s s')
  m_ge_three : ∀ s s' : α, m s s' ≥ 3
    → k s s' * k s' s = 4 * (Real.cos (Real.pi / m s s'))^2 ∧ (0 < k s s')
#check Splitting

def splitting_example : Matrix α α ℝ := fun s s' => match m s s' with
| 1 => -2
| 2 => 0
| 0 => 2
| _ => 2 * Real.cos ( Real.pi / (m s s'))

lemma splitting_example_symmetric (s s': α):
  splitting_example m s s' = splitting_example m s' s := by
  unfold splitting_example
  have := @CoxeterMatrix.symmetric α m mh s s'
  rw [this]

/-- A splitting exists and is given by `splitting_example`. -/
instance : Splitting m (splitting_example m) where
  m_eq_one := by
    intro s s' hyp; unfold splitting_example; split;
    repeat (first | rfl | linarith)
    contradiction
  m_eq_two := by
    intro s s' hyp; unfold splitting_example; split;
    repeat (first | rfl | linarith)
    contradiction
  m_ge_three := by
    intro s s' hyp;
    have : splitting_example m s s' = 2 * Real.cos (Real.pi / (m s s')) := by
      unfold splitting_example; split
      <;> try (first | rfl | linarith)
    rw [splitting_example_symmetric m s' s]
    repeat rw [this]
    apply And.intro
    ring_nf
    simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    apply Real.cos_pos_of_mem_Ioo
    apply And.intro

    have : -(Real.pi / 2) < 0 := by
      apply neg_lt_zero.mpr; apply div_pos; exact Real.pi_pos; norm_num
    have : 0 < Real.pi / (m s s') := by
      apply div_pos; exact Real.pi_pos; rify at hyp; linarith
    linarith
    apply div_lt_div'
    rfl; rify at hyp; linarith; exact Real.pi_pos; norm_num
  m_eq_zero := by
    intro s s' hyp;
    have : splitting_example m s s' = 2 := by
      unfold splitting_example; split
      <;> try (first | rfl | linarith | contradiction)
    rw [splitting_example_symmetric m s' s]
    repeat rw [this]
    apply And.intro <;> linarith

/-
@[simp]
abbrev kk_aux : ℕ → ℝ
| 0 => 3
| 1 => -2
| 2 => 0
| (n + 3) => 2 * Real.cos ( Real.pi / (n+3))


def kk [CoxeterMatrix m] : Matrix α α ℝ := fun s s': α => kk_aux <| m s s'

instance kk.split : Splitting m (kk m) := by sorry
-/
--variable {m : Matrix α  α ℕ} [CoxeterMatrix m]

-- Having established the existence of such a splitting,
-- from now on let k be one such splitting.
variable (k : Matrix α α ℝ) [kh : Splitting m k]

local notation:130 "V⋆" => α → ℝ

/- I cannot seem to find the fact that the set of functions α → ℝ form a vs.-/
instance : (Module ℝ (V⋆)) where
  smul s f m := s * f m
  one_smul := by simp
  mul_smul := by intro x y b; funext s; simp [*]; ring_nf
  smul_zero := by intro x; simp
  zero_smul := by intro x; simp
  smul_add := by intro a x y; simp
  add_smul := by intro r s x; funext c; simp [*]; ring_nf

-- likely there is a need to establish the canonical basis

-- local notation "k" => k m
--local notation:120 a:121 "⋆" => Pi.single a 1

noncomputable def sigma_star (s:α) : (V⋆) →ₗ[ℝ] (V⋆) where
  toFun := fun p =>
    p + (p s) • (∑ s', (k s s') • (fun s'' => if s' = s'' then 1 else 0))
  map_add' := by
    intro x y; funext s'';
    simp only [Pi.add_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    apply_fun (fun z => z - x s'' - y s'')
    ring_nf
    intro a b
    simp
  map_smul' := by
    intro x y; funext s'';
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Finset.sum_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
      RingHom.id_apply]
    apply_fun (fun z => z - x * y s'')
    ring_nf
    intro a b; simp

local notation "σ⋆" => sigma_star k

@[simp]
lemma sigma_star_one {s s': α} {p : V⋆} (hyp : m s s' = 1)
  : (σ⋆ s p) s' = - (p s) := by
  unfold sigma_star
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero]

  have := @Splitting.m_eq_one α m k kh s s' hyp
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, *]
  have := (CoxeterMatrix.one_iff m s s').mp hyp
  rw [this]
  ring_nf


@[simp]
lemma sigma_star_two {s s': α} {p : V⋆} (hyp : m s s' = 2)
  : (σ⋆ s p) s' = p s' := by
  unfold sigma_star
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, add_right_eq_self,
    mul_eq_zero]
  right
  exact @Splitting.m_eq_two α m k kh s s' hyp

@[simp]
lemma sigma_star_value {s s': α} {p : V⋆}
  : (σ⋆ s p) s' = p s' + p s * (k s s') := by
  unfold sigma_star; simp


lemma sigma_star_order_two : (σ⋆ s)^2 = LinearMap.id := by
  apply LinearMap.ext_iff.mpr
  intro p
  funext s'
  simp only [LinearMap.id_coe, id_eq]

  have := @Splitting.m_eq_one _ _ _ kh s s
    ((CoxeterMatrix.one_iff m s s).mpr (by rfl))
  sorry
  -- rw [this]; ring_nf



/-
lemma sigma_star_mul_apply_s'_eq_two  {p : V⋆} (h: m s s' = 2)
  : ((σ⋆ s) * (σ⋆ s')) p s' = - p s' := by sorry


-- add some other lemmas
-- The final goal is
lemma order_sigma_star_mul : orderOf ((σ⋆ s) * (σ⋆ s')) = m s s' := by sorry
-/
end
end GeometricRepresentation


namespace CoxeterMatrix

lemma order_generator_mul (s t :α) :
  orderOf (CoxeterMatrix.of m s * CoxeterMatrix.of m t) = m s t := by sorry

lemma of_injective (a b :α) : of m a = of m b ↔ a = b:= by
  constructor
  . contrapose; intro h; by_contra h2
    have : (of m a) * (of m b) = 1 := by simp [h2]
    rw [<-orderOf_eq_one_iff,order_generator_mul,one_iff] at this
    exact h this
  . intro; congr

end CoxeterMatrix

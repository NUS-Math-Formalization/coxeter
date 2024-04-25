import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.GroupTheory.Coxeter.StandardGeometricRepresentation

/-! # Roots

This material is useful for proving the right exchange property -/

namespace CoxeterSystem

open List Matrix Function Real

variable {B : Type*}
variable {M : CoxeterMatrix B}
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq
local prefix:100 "ρ" => cs.SGR
local prefix:100 "α" => CoxeterMatrix.simpleRoot
local notation:max "⟪"  a  ","  b  "⟫" => M.standardBilinForm a b
local notation "V" => B →₀ ℝ

def roots : Set V := { v | ∃ (w : W) (i : B), v = (ρ w) (α i) }

def rootAbs (v : V) : V := if v > 0 then v else -v

theorem simpleRoot_mem_roots (i : B) : α i ∈ cs.roots := by use 1, i; simp

theorem SGR_apply_simpleRoot_mem_roots (w : W) (i : B) : (ρ w) (α i) ∈ cs.roots :=
  ⟨w, i, rfl⟩

theorem SGR_apply_root_mem_roots (w : W) {v : V} (hv : v ∈ cs.roots) :
    (ρ w) v ∈ cs.roots := by
  obtain ⟨w', i, rfl⟩ := hv
  use w * w', i, by simp only [_root_.map_mul, LinearMap.mul_apply]

theorem neg_roots : -cs.roots = cs.roots := by
  suffices h : cs.roots ⊆ -cs.roots by {
    apply subset_antisymm
    · simpa using Set.neg_subset_neg.mpr h
    · exact h
  }
  rintro _ ⟨w, i, rfl⟩
  use w * (cs.simple i), i
  rw [_root_.map_mul, LinearMap.mul_apply, cs.SGR_simple]
  simp

theorem root_pos_or_neg {v : V} (hv : v ∈ cs.roots) : 0 < v ∨ v < 0 := by
  obtain ⟨w, i, rfl⟩ := hv
  obtain des | not_des := em (cs.IsRightDescent w i)
  · right
    exact (cs.SGR_apply_simpleRoot_neg_iff w i).mpr des
  · left
    exact (cs.SGR_apply_simpleRoot_pos_iff w i).mpr not_des

theorem rootAbs_root_pos {v : V} (hv : v ∈ cs.roots) : 0 < rootAbs v := by
  sorry

/-- Roots are unit vectors -/
theorem standardBilinForm_root_self {v : V} (hv : v ∈ cs.roots) : ⟪v, v⟫ = 1 := by
  obtain ⟨w, i, rfl⟩ := hv
  calc
    _ = ⟪α i, α i⟫        := LinearMap.congr_fun₂ (cs.standardBilinForm_compl₁₂_SGR_apply w) _ _
    _ = 1                 := M.standardBilinForm_simpleRoot_self i

theorem orthogonalReflection_root_eq_iff {v v' : V} (hv : v ∈ cs.roots) (hv' : v' ∈ cs.roots) :
    M.orthoReflection (cs.standardBilinForm_root_self hv) =
      M.orthoReflection (cs.standardBilinForm_root_self hv') ↔
    rootAbs v = rootAbs v' := by
  sorry -- Use CoxeterMatrix.orthoReflection_eq_orthoReflection_iff

theorem standardBilinForm_SGR_apply_simpleRoot_self (w : W) (i : B) :
    ⟪(ρ w) (α i), (ρ w) (α i)⟫ = 1 :=
  cs.standardBilinForm_root_self <| cs.SGR_apply_simpleRoot_mem_roots w i

theorem eq_one_or_eq_neg_one_of_smul_mem_roots {v : V} {μ : ℝ} (hv : v ∈ cs.roots)
    (hμv : μ • v ∈ cs.roots) : μ = 1 ∨ μ = -1 := by
  have := cs.standardBilinForm_root_self hμv
  simp only [LinearMapClass.map_smul, LinearMap.smul_apply, cs.standardBilinForm_root_self hv,
    smul_eq_mul, mul_one] at this
  exact mul_self_eq_one_iff.mp this

theorem eq_simpleRoot_of_pos_of_SGR_simple_apply_neg {v : V} {i : B} (hv : v ∈ cs.roots)
    (v_pos : 0 < v) (iv_neg : (ρ (s i)) v < 0) : v = α i := by
  simp [SGR_simple, CoxeterMatrix.simpleOrthoReflection, CoxeterMatrix.orthoReflection,
    Module.reflection_apply] at iv_neg
  set μ := v i
  have : v = μ • α i := by
    classical
    ext i'
    unfold CoxeterMatrix.simpleRoot
    rw [Finsupp.smul_apply, Finsupp.single_apply]
    split
    · rw [‹i = i'›.symm, smul_eq_mul, mul_one]
    · rw [smul_zero]
      apply _root_.le_antisymm
      · simpa [CoxeterMatrix.simpleRoot, Finsupp.single_apply, if_neg (by assumption)] using iv_neg.le i'
      · exact v_pos.le i'
  obtain one | neg_one :=
    cs.eq_one_or_eq_neg_one_of_smul_mem_roots (cs.simpleRoot_mem_roots i) (this ▸ hv)
  · simpa [one] using this
  · rw [neg_one] at this
    rw [this] at v_pos
    have := v_pos.le i
    simp [CoxeterMatrix.simpleRoot] at this
    absurd this
    linarith

theorem orthoReflection_SGR_reflection_apply (w : W) (i : B) :
    M.orthoReflection (cs.standardBilinForm_SGR_apply_simpleRoot_self w i) = ρ (w * s i * w⁻¹) := by
  apply LinearMap.ext
  intro v
  rw [_root_.map_mul, _root_.map_mul, SGR_simple]
  unfold CoxeterMatrix.simpleOrthoReflection CoxeterMatrix.orthoReflection
    Module.reflection Module.preReflection
  dsimp
  rw [map_sub, _root_.map_smul]
  congr 2
  · rw [← LinearMap.mul_apply, ← _root_.map_mul]
    simp
  · congr 1
    calc
      ⟪(ρ w) (α i), v⟫
      _ = ⟪(ρ w) (α i), (ρ w) ((ρ w⁻¹) v)⟫ := by
        rw [← LinearMap.mul_apply, ← _root_.map_mul]
        simp
      _ = ⟪α i, (ρ w⁻¹) v⟫                 := LinearMap.congr_fun₂ (cs.standardBilinForm_compl₁₂_SGR_apply w) _ _

theorem SGR_apply_simple_eq_iff (w w' : W) (i i' : B) :
    rootAbs ((ρ w) (α i)) = rootAbs ((ρ w') (α i')) ↔ w * s i * w⁻¹ = w' * s i' * w'⁻¹ := by
  /- The previous theorem states that the orthogonal reflection with respect to the vector `(ρ w) (α i)`
  equals `ρ (w * s i * w⁻¹)`. Use `orthogonalReflection_root_eq_iff`. Result follows from injectivity of `ρ` -/
  sorry

/-- The root corresponding to the reflection `t = w * s i * w⁻¹` is `rootAbs ((ρ w) (α i))`.
This is well-defined by the above. -/
def reflectionToRoot (t : cs.reflections) : cs.roots := sorry

theorem reflectionToRoot_pos (t : cs.reflections) : (cs.reflectionToRoot t).val > 0 := sorry

-- If `(ρ w) (cs.reflectionToRoot t).val < 0`, then `t` is a right inversion of `w`
theorem isRightInversion_of_SGR_apply_reflectionToRoot_neg {w : W} (t : cs.reflections)
    (ht : (ρ w) (cs.reflectionToRoot t).val < 0) : cs.IsRightInversion w t := by
  sorry -- Use `cs.simple_induction_left` on the variable `w`, and then use
  -- `cs.eq_simpleRoot_of_pos_of_SGR_simple_apply_neg`

-- `t` is a right inversion of `w` if and only if `(ρ w) (cs.reflectionToRoot t).val < 0`
theorem isRightInversion_iff_SGR_apply_reflectionToRoot_neg {w : W} (t : cs.reflections) :
    (ρ w) (cs.reflectionToRoot t).val < 0 ↔ cs.IsRightInversion w t := by
  sorry -- Idea: apply `isRightInversion_of_SGR_apply_reflectionToRoot_neg` to both `(w, t)` and `(w * t, t)`

-- Next step is to prove that if `(ρ (π ω)) (cs.reflectionToRoot t).val < 0`,
-- then `t` is in the right inversion sequence of `ω`. Use cons-induction on `ω`.
